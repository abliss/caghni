
// A Fact is an "interlingua" object representing a stmt, thm, or defthm. This
// is designed for easy conversion to/from JSON.
// For consistency, you must almways name things in the same order.

module.exports = function(obj) {
    if (!obj) {
        // This is the Fact schema. Only these fields are allowed. Anything
        // undefined may only be set to a string.
        obj = {
            Bone: {
                Stmt: [],
                Hyps: [],
                Free: undefined,
            },
            Meat: {
                Terms: [],
                Kinds: [],
            },
            Skin: {
                Name: undefined,
                License: undefined,
                HypNames: [],
                Delimiters: [],
                DepNames: [],
                V: [],
                T: [],
            },
            Tree: {
                Cmd: undefined,
                Deps: [],
                Proof: [],
                Dkind: undefined,
                Dsig: undefined,
            },
        };
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
    obj.__proto__ = {
        nameTerm: function(s) {
            return indexOf(this.Meat.Terms, s);
        },
        nameHyp: function(s) {
            return 'Hyps.' + indexOf(this.Skin.HypNames, s);
        },
        nameDep: function(s, fact) {
            var that = this;
            return 'Deps.' + indexOf(this.Skin.DepNames, s, function(n) {
                that.Tree.Deps[n] = fact.getKey();
            });
        },
        nameKind: function(s) {
            var that = this;
            return indexOf(this.Meat.Kinds, s, function(n) {
                // New kind added; initialize v and t arrays
                that.Skin.V[n] = [];
                that.Skin.T[n] = [];
            });
        },
        nameVar: function(cmd, kind, s) {
            var key = cmd[0].toUpperCase();
            var kindNum = this.nameKind(kind);
            var varNum = indexOf(this.Skin[key][kindNum], s);
            return key + kindNum + '.' + varNum;
        },
        setName: function(s) {
            this.Skin.Name = s;
            return this;
        },
        setCmd: function(s) {
            this.Tree.Cmd = s;
            return this;
        },
        setHyps: function(arr) {
            this.Bone.Hyps = arr;
            return this;
        },
        setFree: function(arr) {
            this.Bone.Free = arr;
            return this;
        },
        setDkind: function(n) {
            this.Tree.Dkind = n;
            return this;
        },
        setDsig: function(sexp) {
            this.Tree.Dsig = sexp;
            return this;
        },
        setProof: function(arr) {
            this.Tree.Proof = arr;
        },
        setStmt: function(sexp) {
            this.Bone.Stmt = sexp;
        },
        toGhilbert: function(getFact) {
            var that = this;
            function getVar(s) {
                // TODO: insert var/tvar cmds
                var key = s[0];
                var kindNum = s.substring(1).split('.');
                try {
                    return that.Skin[key][kindNum[0]][kindNum[1]];
                } catch (e) {
                    throw new Error("Cannot getVar: " + s + "\n" +
                                    JSON.stringify(that));
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
                    } else if (s.match(/^deps/)) {
                        var depNum = s.substring(5);
                        var depKey = that.Tree.Deps[depNum];
                        var origDep = that.Skin.DepNames[depNum];
                        var depName = getFact(depKey, origDep).Skin.Name;
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
                out += "\n)\n";
            }
            return out;
        },
        getKey: function() {
            var arr = [[this.Bone.Stmt, this.Bone.Hyps, this.Bone.Free],
                       [this.Meat.Terms, this.Meat.Kinds]];
            // TODO: removing quotes and backslashes is convenient, but destroys
            // our ability to move backwards from key to fact, and opens us up
            // to malicious injection. Wise??
            return JSON.stringify(arr).replace(/"/g,"").replace(/\\\\/g, "\\");
        }
    };
    return obj;
}