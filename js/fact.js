(function(module) {
    var CORE_HYPS = 0;
    var CORE_STMT = 1;
    var CORE_FREE = 2;

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
                HypNames: [],
                DepNames: [],
                VarNames: [],
                TermNames: [],
                DefTerm: undefined,  // only for defthms
                Delimiters: [],
            },
            Tree: {
                Cmd: undefined,
                Deps: [],
                Proof: [],
            },
        };
        function copyFromSchema(schemaObj, inputObj, outputObj) {
            for (var k in schemaObj) {
                if (inputObj && inputObj.hasOwnProperty(k)) {
                    if ("object" === typeof schemaObj[k]) {
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
            var termMap = fact.Skin.TermNames.map(function(term) {
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
        this.Core[CORE_HYPS] = arr;
        return this;
    };
    Fact.prototype.setFree = function(arr) {
        this.Core[CORE_FREE] = arr;
        return this;
    };
    Fact.prototype.setDefTerm = function(term) {
        this.Skin.DefTerm = term;
        return this;
    };
    Fact.prototype.setProof = function(arr) {
        this.Tree.Proof = arr;
    };
    Fact.prototype.setStmt = function(sexp) {
        this.Core[CORE_STMT] = sexp;
    };
    Fact.prototype.toGhilbert = function(getFact) { //PICKUP
        var that = this;
        function getVar(s) {
            // TODO: insert var/tvar cmds
            var key = s[0];
            var kindNum = s.substring(1).split('.');
            try {
                return that.Skin[key][kindNum[0]][kindNum[1]];
            } catch (e) {
                // TODO: add this to Skin
                return s;
            }
        }
        function stringify(sexp) {
            if (sexp.shift) {
                var args = sexp.slice(1).map(stringify);
                args.unshift(that.Meat.Terms[sexp[0]]);
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

        if (typeof this.Tree.Dkind === 'number') {
            out += this.Meat.Kinds[this.Tree.Dkind];
            out += " ";
            out += stringify(this.Tree.Dsig);
            out += "\n";
        }
        
        out += '(' + this.Bone.Free.map(function(fv) {
            return '(' + fv.map(getVar).join(' ') + ')';
        }).join(' ') + ')';
        out += "\n  ";
        out += "(";

        for (var i = 0; i < this.Bone.Hyps.length; i++) {
            if (this.Tree.Cmd != 'stmt') {
                out += this.Skin.HypNames[i];
                out += " ";
            }
            out += stringify(this.Bone.Hyps[i]);
            if (i + 1 < this.Bone.Hyps.length) {
                out += "\n   ";
            }
        }
        out += ")";
        out += "\n  ";

        out += stringify(this.Bone.Stmt);
        out += "\n  ";

        if (this.Tree.Proof) {
            function step(s) {
                if (s.shift) {
                    return stringify(s);
                } else if (s.match(/^Hyps/)) {
                    return that.Skin.HypNames[s.substring(5)];
                } else if (s.match(/^Deps/)) {
                    var depNum = s.substring(5);
                    var depMark = that.Tree.Deps[depNum];
                    var origDep = that.Skin.DepNames[depNum];
                    var depName = getFact(depMark, origDep).Skin.Name;
                    return depName;
                } else {
                    var varName = getVar(s);
                    if (!varName) {
                        throw new Exception("bad proof step " + s);
                    }
                    return varName;
                }
            }
            out += this.Tree.Proof.map(step).join(' ');
        }
        out += "\n)\n";
        return out;
    };
    // Returns an appropriate database key, specific to bone and meat.
    Fact.prototype.getKey = function() {
        var key = JSON.stringify(this.Core);
        if (Math.random() < 0.01) {
            console.log("XXXX Key: " + key)
        }
        return key;
    };

    module.exports = Fact;
})(module);