(function(module) {
    function hasOwnProperties(x) {
        for (var k in x) if (x.hasOwnProperty(k)) {
            return true;
        }
        return false;
    }
    // A Fact is an "interlingua" object representing a stmt, thm, or
    // defthm. This is designed for easy conversion to/from JSON.  For
    // consistency, you must almways name things in the same order.  Once the
    // hyps and stmt have been set, further calls to nameKind and nameTerm will
    // not affect the result of getKey().
    function Fact(obj) {

        // This is the Fact schema. Only these fields are allowed. Anything
        // undefined may only be set to a string or, in the case of
        // Tree.Definiendum, an int.
        var schema = {
            Core: [
                [], // Hyps
                [], // Stmt
                [], // Free
            ],
            FreeMaps: {}, // Key is int
            Skin: {
                Name: undefined,
                License: undefined,
                HypNames:[],
                DepNames: [],
                VarNames: [],
                TermNames: [],
                Delimiters: [],
            },
            Tree: {
                Cmd: undefined,
                Definiendum: undefined,  // Defthms: which term is defined?
                Deps: [],
                Proof: [],
            },
        };
        function copyFromSchema(schemaObj, inputObj, outputObj) {
            for (var k in schemaObj) {
                if (inputObj && inputObj.hasOwnProperty(k)) {
                    var s = schemaObj[k];
                    if ((Array.isArray(s) && (s.length > 0)) ||
                        (typeof(s) == 'object' && hasOwnProperties(s))) {
                        outputObj[k] = schemaObj[k];
                        copyFromSchema(schemaObj[k], inputObj[k], outputObj[k]);
                    } else {
                        outputObj[k] = inputObj[k];
                    }
                } else {
                    outputObj[k] = schemaObj[k]
                }
            }
        }
        copyFromSchema(schema, obj, this);
    }

    Fact.CORE_HYPS = 0;
    Fact.CORE_STMT = 1;
    Fact.CORE_FREE = 2;

    // returns the index of s in the array. If necessary, pushes it on the end
    // and calls onAdd(n).
    function indexOf(arr, s, onAdd) {
        for (var i = 0; i < arr.length; i++) {
            if (arr[i] == s) return i;
        }
        var n = arr.push(s) - 1;
        if (onAdd) {
            onAdd(n);
        }
        return n;
    }

    // set up methods on the obj
    Fact.prototype.nameTerm = function(s) {
        return indexOf(this.Skin.TermNames, s);
    };
    Fact.prototype.nameHyp = function(s) {
        return 'Hyps.' + indexOf(this.Skin.HypNames, s);
    };
    Fact.prototype.nameDep = function(s, fact) {
        var that = this;
        return 'Deps.' + indexOf(this.Skin.DepNames, s, function(n) {
            var termMap = fact.getCoreTermNames().map(function(term) {
                return that.nameTerm(term);
            });
            that.Tree.Deps[n] = [fact.Core, termMap]; //TODO: should copy Core
        });
    };
    Fact.prototype.nameVar = function(s) {
        return indexOf(this.Skin.VarNames, s);
    };
    Fact.prototype.setName = function(s) {
        this.Skin.Name = s;
        return this;
    };
    Fact.prototype.setCmd = function(s) {
        this.Tree.Cmd = s;
        return this;
    };
    Fact.prototype.setHyps = function(arr) {
        this.Core[Fact.CORE_HYPS] = arr;
        return this;
    };
    Fact.prototype.setFree = function(arr) {
        this.Core[Fact.CORE_FREE] = arr;
        return this;
    };
    Fact.prototype.setDefiniendum = function(term) {
        this.Tree.Definiendum = this.nameTerm(term);
        return this;
    };
    Fact.prototype.setProof = function(arr) {
        this.Tree.Proof = arr;
    };
    Fact.prototype.setStmt = function(sexp) {
        this.Core[Fact.CORE_STMT] = sexp;
    };
    // Returns a subexpression whose first element is the given term.
    function findSubExpWithTerm(sexp, term) {
        // TODO: unexceptional exception
        function recurse(subexp) {
            if (Array.isArray(subexp)) {
                if (subexp[0] == term) throw(subexp);
                subexp.slice(1).map(recurse);
            }
        }
        try { recurse(sexp); }
        catch (e) { return e; }
        throw new Error("Term not found! " + term + " in " +
                        JSON.stringify(sexp));
    };
    Fact.prototype.toGhilbert = function(context, toGhilbertCb) {
        //console.log("# XXXX toGhilbert: " + this.Skin.Name);
        var that = this;
        var out = "";
        function getVar(s) {
            // TODO: insert var/tvar cmds
            return that.Skin.VarNames[s];
        }
        function stringify(sexp) {
            if (sexp.slice) {
                var args = sexp.slice(1).map(stringify);
                args.unshift(that.Skin.TermNames[sexp[0]]);
                return "(" + args.join(" ") + ")";
            } else {
                return getVar(sexp);
            }
        }

        out += this.Tree.Cmd
        out += " ";
        out += "(" + this.Skin.Name;
        out += "\n  ";

        if (this.Tree.Cmd == 'defthm') {
            out += " k " + "\n"; // TODO: kinds
            // infer the dsig by grabbing a subexp with the required term
            var dsig = findSubExpWithTerm(this.Core[Fact.CORE_STMT],
                                          this.Tree.Definiendum);
            out += stringify(dsig) + "\n  ";
        }

        out += '(' + this.Core[Fact.CORE_FREE].map(function(fv) {
            return '(' + fv.map(getVar).join(' ') + ')';
        }).join(' ') + ')';
        out += "\n  ";
        out += "(";

        for (var i = 0; i < this.Core[Fact.CORE_HYPS].length; i++) {
            if (this.Tree.Cmd != 'stmt') {
                out += this.Skin.HypNames[i];
                out += " ";
            }
            out += stringify(this.Core[Fact.CORE_HYPS][i]);
            if (i + 1 < this.Core[Fact.CORE_HYPS].length) {
                out += "\n   ";
            }
        }
        out += ")";
        out += "\n  ";

        out += stringify(this.Core[Fact.CORE_STMT]);
        out += "\n  ";

        if (this.Tree.Proof) {
            var outstandingQueries = 0;
            var finishedQuerying = false;
            var depNames = [];
            var mapped = [];
            function finish() {
                out += mapped.join(' ') + "\n)\n";
                toGhilbertCb(null, out);
            }
            function step(s) {
                if (!s.match) {
                    return stringify(s);
                } else if (s.match(/^Hyps/)) {
                    return that.Skin.HypNames[s.substring(5)];
                } else if (s.match(/^Deps/)) {
                    var depNum = s.substring(5);
                    var depCore = that.Tree.Deps[depNum][0];
                    var depMap = that.Tree.Deps[depNum][1]; //XXX
                    var origDep = that.Skin.DepNames[depNum];
                    if (!depNames[depNum]) {
                        depNames[depNum] = {toString: function() {
                            return this.name || "WTF";
                        }}
                        outstandingQueries++;
                        var hint = {name:origDep};
                        hint.terms = depMap.map(function(n) {
                            return that.Skin.TermNames[n];});
                        /*
                        console.log("# XXXX Gh " +
                                    that.Skin.Name + " wants " +
                                    hint.name);
*/
                        context.requestFact(
                            depCore, hint,
                            function(err, fact) {
                                if (err) {
                                    toGhilbertCb(err, null);
                                } else {
                                    depNames[depNum].name = fact.Skin.Name;
                                    outstandingQueries--;
/*
                                    console.log("# XXXX Gh " +
                                                that.Skin.Name +
                                                " got " + fact.Skin.Name +
                                                " wants " + outstandingQueries);
*/
                                    if (finishedQuerying &&
                                        (outstandingQueries == 0)) {
                                        finish();
                                    }
                                }
                            });
                    }
                    return depNames[depNum];
                }
            }
            mapped = that.Tree.Proof.map(step);
            finishedQuerying = true;
            if (outstandingQueries == 0) {
                finish();
            }
        }
    };
    Fact.prototype.getNewTerm = function() {
        if (this.Tree.Cmd != 'defthm') {
            return null;
        }
        return this.Skin.TermNames[this.Tree.Definiendum];
    };
    // Returns an appropriate database key, specific to the core
    Fact.prototype.getKey = function() {
        var key = this.getMark();
        if (Math.random() < 0.01) {
            console.log("XXXX Key: " + key)
        }
        return key;
    };
    // Returns the prefix of this.Skin.TermNames which is used in the Core.
    Fact.prototype.getCoreTermNames = function() {
        // TODO: this is a little hacky...
        var maxOp = -1;
        function scan(exp) {
            if (exp.slice) {
                if (exp[0] > maxOp) {
                    maxOp = exp[0];
                }
                exp.slice(1).map(scan);
            }
        }
        this.Core[Fact.CORE_HYPS].forEach(scan);
        scan(this.Core[Fact.CORE_STMT]);
        return this.Skin.TermNames.slice(0, maxOp + 1);
    };
    Fact.prototype.getMark = function() {
        return JSON.stringify(this.Core) + ";" +
            JSON.stringify(this.getCoreTermNames());
    };
    Fact.prototype.ensureFree = function(termVar, bindingVar) {
        if (Array.isArray(termVar) || Array.isArray(bindingVar)) {
            throw new Error("Expected vars: " + JSON.stringify(termVar) +
                            " " + JSON.stringify(bindingVar));
        }
        var myFree = this.Core[Fact.CORE_FREE];
        var freeList;
        var firstIndexBigger = myFree.length;
        // Keeps the list sorted if it already was.
        for (var i = 0; i < myFree.length; i++) {
            if (myFree[i][0] == termVar) {
                freeList = myFree[i];
                break;
            } else if (myFree[i][0] > termVar) {
                firstIndexBigger = i;
            }
        }
        if (!freeList) {
            freeList = [termVar];
            myFree.splice(firstIndexBigger, 0, freeList);
        }
        firstIndexBigger = freeList.length;
        for (var i = 1; i < freeList.length; i++) {
            if (freeList[i] == bindingVar) {
                // Already there. Nothing to do.
                return;
            } else if (freeList[i] > bindingVar) {
                firstIndexBigger = i;
            }
        }
        freeList.splice(firstIndexBigger, 0, bindingVar);
    };

    function termEqual(t1, t2) {
         // TODO: faster to use JSON.stringify?
        if (Array.isArray(t1)) {
            if (t1.length !== t2.length) {
                return false;
            }
            for (var i = 0; i < t1.length; i++) {
                if (!termEqual(t1[i], t2[i])) {
                    return false;
                }
            }
            return true;
        } else {
            return t1 === t2;
        }
    }

    // Not a full unification; information flows only one way
    function unify(src, dst, varMap, opMap) {
        if (Array.isArray(src)) {
            var opNum = src[0];
            if (opMap) {
                opNum = opMap[opNum];
            }
            if (!Array.isArray(dst) ||
                (src.length !== dst.length) ||
                (dst[0] !== opNum)) {
                console.log("XXX3 " + JSON.stringify(src) + " != " + JSON.stringify(dst));
                return false;
            }
            for (var i = 1; i < src.length; i++) {
                if (!unify(src[i], dst[i], varMap, opMap)) {
                console.log("XXX2 " + JSON.stringify(src) + " != " + JSON.stringify(dst));           return false;
                }
            }
            return true;
        } else {
            if (varMap.hasOwnProperty(src)) {
                src = varMap[src];
                if (!termEqual(src, dst)) {
                    console.log("XXX1 " + JSON.stringify(src) + " != " + JSON.stringify(dst));
                    return false;
                }
                return true;
            } else {
                varMap[src] = dst;
                return true;
            }
        }
    }

    // asserts that bindingVar must not appear free in exp, with respect to the
    // given constraints. If possible, add constraints to ctx.notFreeMap to
    // guarantee this, and return true. If not possible (e.g. explicit
    // freeness detected), return false.
    function assertNotFreeIn(ctx, bindingVar, exp) {
        if (Array.isArray(exp)) {
            // By default, bVar is free in exp if it is free in SOME of the
            // args.  BUT, if the term exp[0] has a freeMap, it might be the
            // case that bVar is bound.

            // Each boundList means: bVar is NOT free in exp, UNLESS it is also
            // free in SOME of exps of the boundList. This UNLESS clause
            // must trigger for EVERY boundList (if there are any) in order for
            // bVar to be free in exp.
            var boundLists = [];
            var freeMap = ctx.fact.FreeMaps[exp[0]];
            if (freeMap != undefined) {
                exp.slice(1).forEach(function(arg, argNum) {
                    if (arg == bindingVar) {
                        var boundList = freeMap[argNum];
                        if (boundList != undefined) {
                            // Okay, the bVar has been found as a "binding arg".
                            boundLists.push(boundList.map(function(argNum) {
                                return exp[argNum + 1];
                            }));
                        }
                    }
                });
            }
            var recurse = assertNotFreeIn.bind(null, ctx, bindingVar);
            if (boundLists.length == 0) {
                // If there were no boundLists, just check each arg.
                return exp.slice(1).every(recurse);
            } else if (boundLists.length > 1) {
                // This is tricky... only ONE of the boundLists needs to succeed,
                // but the others would add spurious constraints to the ctx.
                // TODO: Does anyone ever even need this?
                throw new Error("Not Implemented!");
            } else {
                // Check each arg in the boundList.
                return boundLists[0].every(recurse);
            }
        } else {
            // exp is a Var.
            if (bindingVar == exp) {
                // Explicitly free
                return false;
            } else if (!ctx.nonDummyVars[bindingVar] || !ctx.nonDummyVars[exp]) {
                // Each Proof Dummy Variable is assumed disjoint-from each other
                // variable. (I.e., neither appears-free-in the other.)
                return true;
            } else {
                // Note: we do not here distinguish between binding vars and
                // term vars. We put pairs of binding-vars in the notFreeMap,
                // which Ghilbert does not allow, and trust they will be
                // filtered out later.
                ctx.notFreeMap[[bindingVar, exp]] = 1;
                return true;
            }
        }
    }

    // Visit each var in the given expression. Update ctx.bindingVars for any
    // vars which must be binding due to a freemap entry. If callback is passed,
    // also call it on each var.
    function visitVars(ctx, callback, exp) {
        if (Array.isArray(exp)) {
            exp.slice(1).forEach(visitVars.bind(null, ctx, callback));
            var freeMap = ctx.fact.FreeMaps[exp[0]];
            if (freeMap !== undefined) {
                for (var k in freeMap) if (freeMap.hasOwnProperty(k)) {
                    var arg = exp[Number(k) + 1];
                    if (Array.isArray(arg)) {
                        throw new Error("Term " + JSON.stringify(arg) +
                                        " passed as arg " + k + " to " + 
                                        ctx.fact.Skin.TermNames[exp[0]]);
                    }
                    ctx.bindingVars[arg] = true;
                }
            }
        } else {
            if (callback) {
                callback(exp);
            }
        }
    }

    function reduceProofStep(ctx, step, index) {
        if (!ctx.fact) {
            // On first call, accumulator contains only fact
            ctx = {fact:ctx, stack:[], mandHyps:[], notFreeMap:{},
                   nonDummyVars: {}, bindingVars: {}};

            // Find out which vars are Not Proof Dummy Vars, and which vars
            // are Binding Vars.
            // NOTE: we only mark a var as Binding if it is used as a binding
            // arg to some term in the FreeMaps, in either a hyp or the conc.
            // Otherwise we assume it is term.
            // TODO: This could create a problem ... e.g. sbaxex. but usually(?)
            // in a case where the thm proved was not as general as it should
            // have been!
            // TODO: this could be made faster using our assumption of sorted
            // int varnames.
            var markNonDummy = visitVars.bind(null, ctx, function(v) {
                ctx.nonDummyVars[v] = true;
            });
            markNonDummy(ctx.fact.Core[Fact.CORE_STMT]);
            ctx.fact.Core[Fact.CORE_HYPS].forEach(markNonDummy);
        }
        if (typeof step === "string") {
            var parts = step.split(/\./);
            var num = Number(parts[1]);
            switch(parts[0]) {
            case "Deps":
                var dep = ctx.fact.Tree.Deps[num];
                var depCore = dep[0];
                var opMap = dep[1];
                var varMap = {}; // from dep vars to terms in fact vars
                // Map vars present in hyps by one-way unification
                depCore[Fact.CORE_HYPS].reduceRight(function(ignored, hyp) {
                    if (ctx.stack.length == 0) {
                        throw new Error("Stack underflow: step " + step);
                    } else if (!unify(hyp, ctx.stack.pop(), varMap, opMap)) {
                        throw new Error("Hyp unify fail: step " + step);
                    }
                }, undefined);
                // Map remaining vars in stmt using mandhyps
                function substitute(term) {
                    if (Array.isArray(term)) {
                        var opNum = opMap[term[0]];
                        var out = term.slice(1).map(substitute);
                        out.unshift(opNum);
                        return out;
                    } else if (varMap.hasOwnProperty(term)) {
                        return varMap[term];
                    } else {
                        if (ctx.mandHyps.length == 0) {
                            throw new Error("Too few mandhyps! term " + term);
                        }
                        var mandHyp = ctx.mandHyps.shift();
                        varMap[term] = mandHyp;
                        return mandHyp;
                    }
                }
                var newStackExp = substitute(depCore[Fact.CORE_STMT]);
                // Now that varMap is complete, check it against the dep's free
                // constraints.
                depCore[Fact.CORE_FREE].forEach(function(flist) {
                    var term = varMap[flist[0]];
                    flist.slice(1).forEach(function(bvar) {
                        var newBvar = varMap[bvar];
                        if (Array.isArray(newBvar)) {
                            throw new Error("Expected binding var for " + bvar +
                                            "; got " + JSON.stringify(newBvar));
                        }
                        ctx.bindingVars[newBvar] = true;
                        if (!assertNotFreeIn(ctx, newBvar, term)) {
                            throw new Error("Freeness violation! " + newBvar +
                                            " free in " + JSON.stringify(term) +
                                            " at step " + step  + "@" + index);
                        }
                    });
                });
                // This step may have thrust some variable into a binding
                // position in one of our terms.
                visitVars(ctx, null, newStackExp);
                ctx.stack.push(newStackExp);
                break;
            case "Hyps":
                var hypArr = ctx.fact.Core[Fact.CORE_HYPS];
                if (num >= hypArr.length) {
                    throw new Error("Bad Hyp " + step + " at " + index);
                }
                ctx.stack.push(hypArr[num]);
                break;
            default:
                throw new Error("Unknown string step " + step + " at " + index);
            }
            ctx.mandHyps = [];
        } else {
            ctx.mandHyps.push(step);
        }
        return ctx;
    }

    // Matches the remnant (what's left on the proof stack) against a defthm's
    // declared conclusion (the STMT of the core). Checks for consistency in all
    // uses of the definition substitution, and writes to ctx.defSig and
    // ctx.definiens. Throws up on any inconsistency. Does NOT check for
    // soundness or freeness.
    function defConcMatch(provedTerm, declaredTerm, fact, ctx) {
        if (Array.isArray(provedTerm) != Array.isArray(declaredTerm)) {
            throw new Error("Defthm conclusion mismatch: isArray");
        }
        if (Array.isArray(provedTerm)) {
            if (provedTerm[0] == declaredTerm[0]) {
                if (provedTerm.length != declaredTerm.length) {
                    throw new Error("Defthm conclusion mismatch: length");
                }
                for (var i = 1; i < provedTerm.length; i++) {
                    defConcMatch(provedTerm[i], declaredTerm[i], fact, ctx);
                }
                return;
            } else if (declaredTerm[0] != fact.Tree.Definiendum) {
                throw new Error("Defthm conclusion mismatch: Definiendum");
            } else {
                if (ctx.hasOwnProperty("defSig")) {
                    if (ctx.defSig.length != declaredTerm.length) {
                        throw new Error("Defthm conclusion mismatch: defSig.l");
                    }
                    for (var i = 1; i < declaredTerm.length; i++) {
                        if (declaredTerm[i] !== ctx.defSig[i]) {
                            throw new Error("Defthm conclusion mismatch:" +
                                            " defSig inconsistent");
                        }
                    }
                    if (!termEqual(ctx.definiens, provedTerm)) {
                        throw new Error("Defthm conclusion mismatch:" +
                                        " definiens inconsistent");
                    }
                    return;
                } else {
                    // OK, this is the first time we've seen the definiens.
                    // Actual validity checked elsewhere.
                    ctx.defSig = declaredTerm;
                    ctx.definiens = provedTerm;
                    return;
                }
            }
        } else {
            if (provedTerm !== declaredTerm) {
                throw new Error("Defthm conclusion mismatch: eq");
            }
        }
    }

    // Checks the Tree for proof integrity; throws up any error.
    Fact.prototype.verify = function() {
        switch (this.Tree.Cmd) {
        case 'stmt':
            return;
        case 'defthm':
        case 'thm':
            var ctx = this.Tree.Proof.reduce(reduceProofStep, this);
            if (ctx.stack.length != 1) {
                throw new Error("Final stack length " + ctx.stack.length);
            } else if (this.Tree.Cmd == 'thm') {
                if (!unify(ctx.stack[0], this.Core[Fact.CORE_STMT], {})) {
                    throw new Error(
                        "Thm Mismatch: Final stack has " +
                            JSON.stringify(ctx.stack[0]) + " but wanted " +
                            JSON.stringify(this.Core[Fact.CORE_STMT]));
                    // TODO: We allow you to prove something more general than
                    // you stated... but this is a bad idea and will not verify
                    // in gh
                } else {
                    // defthm
                }
            } else {
                defConcMatch(ctx.stack[0], this.Core[Fact.CORE_STMT], this,ctx);
                if (!ctx.hasOwnProperty("defSig")) {
                    throw new Error("Term being defined does not occur.");
                }
                // TODO: PICKUP: check soundness
            }
            // Check the accumulated freeness constraints against the declared
            // ones.
            var pairs = [];
            for (var p in ctx.notFreeMap) if (ctx.notFreeMap.hasOwnProperty(p)) {
                // Ignore pairs where the second var has been detected as a 
                // binding var.
                var pair = p.split(',');
                if (!ctx.bindingVars[pair[1]]) {
                    pairs.push(p);
                }
            }
            pairs.sort();
            var declaredPairs = [];
            ctx.fact.Core[Fact.CORE_FREE].forEach(function(flist) {
                var term = flist[0];
                flist.slice(1).forEach(function(bvar) {
                    declaredPairs.push(bvar + "," + term);
                });
            });
            declaredPairs.sort();
            var calculated = JSON.stringify(pairs);
            var declared = JSON.stringify(declaredPairs);
            if (calculated != declared) {
                throw new Error("Freeness constraint mismatch: calculated " +
                                calculated + "; declared " + declared);
            }
            return;
        default:
            throw new Error("Unknown cmd " + this.Tree.Cmd);
        }
    };
    module.exports = Fact;
})(module);
