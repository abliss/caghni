(function(module) {
    // A Fact is an "interlingua" object representing a stmt, thm, or
    // defthm. This is designed for easy conversion to/from JSON.  For
    // consistency, you must almways name things in the same order.  Once the
    // hyps and stmt have been set, further calls to nameKind and nameTerm will
    // not affect the result of getKey().
    function Fact(obj) {

        // This is the Fact schema. Only these fields are allowed. Anything
        // undefined may only be set to a string.
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
                Definiendum: [],  // only for defthms
                Deps: [],
                Proof: [],
            },
        };
        function copyFromSchema(schemaObj, inputObj, outputObj) {
            for (var k in schemaObj) {
                if (inputObj && inputObj.hasOwnProperty(k)) {
                    var s = schemaObj[k];
                    if ((Array.isArray(s) && (s.length > 0)) ||
                        (!Array.isArray(s) && s)) {
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
    Fact.prototype.setDefiniendum = function(exp) {
        this.Tree.Definiendum = exp;
        return this;
    };
    Fact.prototype.setProof = function(arr) {
        this.Tree.Proof = arr;
    };
    Fact.prototype.setStmt = function(sexp) {
        this.Core[Fact.CORE_STMT] = sexp;
    };
    Fact.prototype.toGhilbert = function(context, toGhilbertCb) {
        //console.log("# XXXX toGhilbert: " + this.Skin.Name);
        var that = this;
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
        var out = "";
        out += this.Tree.Cmd
        out += " ";
        out += "(" + this.Skin.Name;
        out += "\n  ";

        if (this.Tree.Cmd == 'defthm') {
            out += " k " + "\n"; // TODO: kinds
            out += stringify(this.Tree.Definiendum) + "\n  ";
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
        return this.Skin.TermNames[this.Tree.Definiendum[0]];
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

    module.exports = Fact;
})(module);