(function(module) {
    function hasOwnProperties(x) {
        for (var k in x) if (x.hasOwnProperty(k)) {
            return true;
        }
        return false;
    }
    // A Fact is an "interlingua" object representing a stmt, thm, or
    // defthm. This is designed for easy conversion to/from JSON.  For
    // consistency, you must always name things in the same order.  Once the
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
            // FreeMaps should have the same length as Skin.TermNames: i.e., one
            // FreeMap for every term T used in this fact (even if not in the
            // core). A FreeMap is a list whose length is at most the arity of
            // the corresponding term; each element is a "bindingList" for the
            // corresponding arg. (If an arg is a term var rather than a binding
            // var, its bindingList is "null"; a suffix of nulls may be
            // truncated.)
            
            // The bindingList for a bindingVar (call it "x") is a
            // sorted list of distinct 0-indexed arg numbers n. x is considered
            // "not free in T" unless x appears free in EACH arg n.
            // 
            // An example from sbceq12:
            // Skin.TermNames:["->","=","<->","[/]"     ,"rwff","A."]
            //       FreeMaps:[ [] ,[] , []  ,[null,[0]], [[]], [[]] ]
            FreeMaps: [], 
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
    Fact.prototype.nameTerm = function(s, freeMap) {
        if (typeof freeMap == 'undefined') {
            throw new Error("freeMap needed to name " + s);
        }
        var that = this;
        var added = false;
        var name = indexOf(this.Skin.TermNames, s, function(n) {
            // TODO: shoud clone freeMap
            that.FreeMaps[n] = freeMap;
            added = true;
        });
        if (!added &&
            (JSON.stringify(this.FreeMaps[name]) !=
             JSON.stringify(freeMap))) {
            // TODO: create new term with same name??
            throw new Error("freeMap mismatch for " + s + ": had " + 
                            JSON.stringify(this.FreeMaps[name]) + " new " +
                            JSON.stringify(freeMap));
        }
        return name;
    };
    Fact.prototype.nameHyp = function(s) {
        return 'Hyps.' + indexOf(this.Skin.HypNames, s);
    };
    Fact.prototype.nameDep = function(s, fact) {
        var that = this;
        return 'Deps.' + indexOf(this.Skin.DepNames, s, function(n) {
            var termMap = [];
            fact.getCoreTermNames().forEach(function(name, num) {
                termMap[num] = that.nameTerm(name, fact.FreeMaps[num]);
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
    Fact.prototype.setDefiniendum = function(termNum) {
        this.Tree.Definiendum = termNum;
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
                        hint.freeMaps = depMap.map(function(n) {
                            return that.FreeMaps[n];});
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
                return false;
            }
            for (var i = 1; i < src.length; i++) {
                if (!unify(src[i], dst[i], varMap, opMap)) {
                    return false;
                }
            }
            return true;
        } else {
            if (varMap.hasOwnProperty(src)) {
                src = varMap[src];
                if (!termEqual(src, dst)) {
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
            if (freeMap != null) {
                exp.slice(1).forEach(function(arg, argNum) {
                    if (arg == bindingVar) {
                        var boundList = freeMap[argNum];
                        if (boundList != null) {
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
            if (ctx.ensureFree) {
                // Hook to allow custom resolution; used in computing freemaps
                // when verifying defthms
                return ctx.ensureFree(bindingVar, exp);
            } else if (bindingVar == exp) {
                // Explicitly free
                return false;
            } else if (!ctx.nonDummyVars[bindingVar] ||
                       !ctx.nonDummyVars[exp]) {
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
            freeMap.forEach(function(bindingList, argNum) {
                var arg = exp[argNum + 1];
                if (Array.isArray(arg)) {
                    throw new Error("Term " + JSON.stringify(arg) +
                                    " passed as arg " + k + " to " + 
                                    ctx.fact.Skin.TermNames[exp[0]]);
                }
                ctx.bindingVars[arg] = true;
            });
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

            // Find out which vars are Not Proof Dummy Vars.
            // TODO: this could be made faster using our assumption of sorted
            // int varnames.
            var markNonDummy = visitVars.bind(null, ctx, function(v) {
                ctx.nonDummyVars[v] = true;
            });
            markNonDummy(ctx.fact.Core[Fact.CORE_STMT]);
            ctx.fact.Core[Fact.CORE_HYPS].forEach(markNonDummy);

            // NOTE: we only mark a var as Binding if it is used as a binding
            // arg to some term in the FreeMaps, in either a hypothesis, the
            // conclusion, or an expression pushed onto the proof stack.
            // Otherwise we assume it is a Term var.

            // TODO: This could create a problem. E.g. sbaxex. but usually
            // (always?) in a case where the thm proved was not as general as
            // it should have been!
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
                if (ctx.mandHyps.length != 0) {
                    throw new Error("Too many mand hyps! step " + index);
                }
                // Now the varMap is complete.

                // Ghilbert does not allow the same var to be substituted
                // for two different binding variables. So we need to figure out
                // which vars are binding in the dependency fact. TODO: what if
                // the fact declared binding vars in a way that can't be
                // inferred from the core??
                
                // TODO: ugly hack. Need to refine visitVars API.
                var depCtx = {bindingVars:{}, fact:{FreeMaps:[]}};
                opMap.forEach(function(myNum, eirNum) {
                    depCtx.fact.FreeMaps[eirNum] = ctx.fact.FreeMaps[myNum];
                });
                var depVisitor = visitVars.bind(null, depCtx, null);
                depCore[Fact.CORE_HYPS].forEach(depVisitor);
                depVisitor(depCore[Fact.CORE_STMT]);

                // Check completed varMap against the dep's free constraints.
                depCore[Fact.CORE_FREE].forEach(function(flist) {
                    var term = varMap[flist[0]];
                    flist.slice(1).forEach(function(bvar) {
                        depCtx.bindingVars[bvar] = true;
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
                
                // Now check for collisions in substituted binding-vars
                var bindingVarsUsed = {};
                for (var v in depCtx.bindingVars) {
                    if (depCtx.bindingVars.hasOwnProperty(v)) {
                        var myBvar = varMap[v];
                        if (bindingVarsUsed[myBvar]) {
                            throw new Error("Binding variables not distinct: "
                                            + term + " at step " + index);
                        }
                        bindingVarsUsed[myBvar] = true;
                    }
                }
                
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

    // Checks the Tree for proof integrity; throws up any error. If successful
    // (and if the fact is not a stmt), returns an object with some verification
    // context. In particular, it contains the set of bindingVars.
    Fact.prototype.verify = function() {
        switch (this.Tree.Cmd) {
        case 'stmt':
            return;
        case 'defthm':
        case 'thm':
            var ctx = this.Tree.Proof.reduce(reduceProofStep, this);
            if (ctx.stack.length != 1) {
                throw new Error("Final stack length " + ctx.stack.length);
            } else if (ctx.mandHyps.length != 0) {
                throw new Error("Leftover mand hyp on stack");
            } else if (this.Tree.Cmd == 'thm') {
                var varMap = {};
                if (!unify(ctx.stack[0], this.Core[Fact.CORE_STMT], varMap)) {
                    throw new Error(
                        "Thm Mismatch: Final stack has " +
                            JSON.stringify(ctx.stack[0]) + " but wanted " +
                            JSON.stringify(this.Core[Fact.CORE_STMT]));
                }
                // You might have proved something too general.
                for (var v in varMap) if (varMap.hasOwnProperty(v)) {
                    if (Number(v) !== varMap[v]) {
                        throw new Error("Stack doesn't match concl");
                    }
                }
            } else { // BEGIN defthm handling
                defConcMatch(ctx.stack[0], this.Core[Fact.CORE_STMT], this,ctx);
                if (!ctx.hasOwnProperty("defSig")) {
                    throw new Error("Term being defined does not occur.");
                }
                // Ghilbert has a few more restrictions on defthms to guarantee
                // soundness:
       // - all formal arguments of the definition term occur in remnant
       // - For any variable v occurring in remnant that isn't one of the formal
       //   arguments, all of the following hold:
       //   - v is a proof dummy variable (doesn't occur in hypotheses or
       //     conclusion
       //   - v is a binding variable
       //   - v does not occur free in the remnant.
                if (!Array.isArray(ctx.definiens)) {
                    throw new Error("Definiens is var: " + ctx.definiens);
                }
                var formalArgs = {};
                var bindingFormalArg = null;
                ctx.defSig.slice(1).forEach(function(v, index) {
                    if (Array.isArray(v)) {
                        throw new Error("Defthm formal arg term " + v);
                    } else if (formalArgs.hasOwnProperty(v)) {
                        throw new Error("Defthm repeated formal arg " + v);
                    }
                    formalArgs[v] = index;
                    if (ctx.bindingVars[v]) {
                        // Ghilbert allows two binding formal args if they are
                        // different kinds, but we have no kinds here.
                        if (bindingFormalArg) {
                            throw new Error("Defthm has two binding vars: " +
                                            bindingFormalArg + " and " + v);
                        }
                        bindingFormalArg = v;
                    }
                });

                var remnantVars = {};
                var seenVars = {};
                function checkVar(v) {
                    if (!remnantVars[v]) {
                        remnantVars[v] = 1;
                        if (formalArgs.hasOwnProperty(v)) {
                            seenVars[v] = true;
                        } else {
                            if (ctx.nonDummyVars[v]) {
                                throw new Error("Var " + v +
                                                " isn't a defthm arg or dummy");
                            } else if (!ctx.bindingVars[v]) {
                                throw new Error("Var " + v +
                                                " isn't a binding var");
                            } else if (!assertNotFreeIn(ctx, v,ctx.definiens)) {
                                throw new Error("Var " + v +
                                                " appears free in remnant");
                            }
                        }
                    }
                }
                
                visitVars(ctx, checkVar, ctx.definiens);
                ctx.defSig.slice(1).forEach(function(v) {
                    if (!seenVars[v]) {
                        throw new Error("Unused Defthm Formal arg " + v);
                    }
                });

                // Now we need to check that the freemap of the new term is
                // correct.
                var newFreeMap = this.FreeMaps[this.Tree.Definiendum];
                var checkedVars = {};
                for (var v in ctx.bindingVars) {
                    if (ctx.bindingVars.hasOwnProperty(v) &&
                        formalArgs.hasOwnProperty(v)) {
                        if (newFreeMap[v] == null) {
                            throw new Error("bvar " + v + " not in freemap");
                        }
                        var bindingList = newFreeMap[v];
                        // this says: v is bound in defSig UNLESS v is free in
                        // EVERY bindingList arg.
                        var computed = [], seen = {};
                        ctx.ensureFree = function(bVar, tVar) {
                            if (formalArgs.hasOwnProperty(tVar) &&
                                !seen[tVar]) {
                                computed.push(formalArgs[tVar]);
                                seen[tVar] = true;
                            }
                            // If this tVar appears in the definiens but not
                            // the defSig, it must be a binding dummy var, so
                            // no worries.
                            return true;
                        };
                        assertNotFreeIn(ctx, v, ctx.definiens); // can't fail
                        delete ctx.ensureFree;
                        computed.sort();
                        if (JSON.stringify(computed) !==
                            JSON.stringify(bindingList)) {
                            throw new Error("Freemap mismatch for " + v + ":" +
                                            computed + " != " + bindingList);
                        }
                        checkedVars[v] = true;
                    }
                }
                newFreeMap.forEach(function(bindingList, argNum) {
                    if ((bindingList != null) && !checkedVars[argNum]) {
                        throw new Error("Spurious arg in freemap: " + argNum);
                    }
                });
            } // END defthm handling
            
            // Check the accumulated freeness constraints against the declared
            // ones.
            var pairs = [];
            for (var p in ctx.notFreeMap) if (ctx.notFreeMap.hasOwnProperty(p)){
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
                if (!ctx.bindingVars[term]) {
                    flist.slice(1).forEach(function(bvar) {
                        declaredPairs.push(bvar + "," + term);
                    });
                }
            });
            declaredPairs.sort();
            var calculated = JSON.stringify(pairs);
            var declared = JSON.stringify(declaredPairs);
            if (calculated != declared) {
                var err =  new Error("Freeness constraint mismatch: calculated " +
                                     calculated + "; declared " + declared);
                err.calculated = pairs;
                err.declared = declaredPairs;
                err.context = ctx;
                throw(err);
            }
            return ctx;
        default:
            throw new Error("Unknown cmd " + this.Tree.Cmd);
        }
    };
    module.exports = Fact;
})(module);
