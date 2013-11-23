// A Fact is an "interlingua" object representing a stmt, thm, or defthm. This
// is designed for easy conversion to/from JSON.
// For consistency, you must almways name things in the same order.

module.exports = function(obj) {
    if (!obj) {
        // This is the Fact schema. Only these fields are allowed. Anything
        // undefined may only be set to a string.
        obj = {
            bone: {
                stmt: [],
                hyps: [],
                free: undefined,
            },
            meat: {
                terms: [],
                kinds: [],
            },
            skin: {
                name: undefined,
                license: undefined,
                hypNames: [],
                delimiters: [],
                depNames: [],
                v: [],
                t: [],
            },
            tree: {
                cmd: undefined,
                deps: [],
                proof: [],
                dkind: undefined,
                dsig: undefined,
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
            return indexOf(this.meat.terms, s);
        },
        nameHyp: function(s) {
            return 'hyps.' + indexOf(this.skin.hypNames, s);
        },
        nameDep: function(s, fact) {
            var that = this;
            return 'deps.' + indexOf(this.skin.depNames, s, function(n) {
                that.tree.deps[n] = fact.getKey();
            });
        },
        nameKind: function(s) {
            var that = this;
            return indexOf(this.meat.kinds, s, function(n) {
                // New kind added; initialize v and t arrays
                that.skin.v[n] = [];
                that.skin.t[n] = [];
            });
        },
        nameVar: function(cmd, kind, s) {
            var key = cmd[0];
            var kindNum = this.nameKind(kind);
            var varNum = indexOf(this.skin[key][kindNum], s);
            return key + kindNum + '.' + varNum;
        },
        setName: function(s) {
            this.skin.name = s;
            return this;
        },
        setCmd: function(s) {
            this.tree.cmd = s;
            return this;
        },
        setHyps: function(arr) {
            this.bone.hyps = arr;
            return this;
        },
        setFree: function(arr) {
            this.bone.free = arr;
            return this;
        },
        setDkind: function(n) {
            this.tree.dkind = n;
            return this;
        },
        setDsig: function(sexp) {
            this.tree.dsig = sexp;
            return this;
        },
        setProof: function(arr) {
            this.tree.proof = arr;
        },
        setStmt: function(sexp) {
            this.bone.stmt = sexp;
        },
        toGhilbert: function(factsByKey) {
            var that = this;
            function getVar(s) {
                // TODO: insert var/tvar cmds
                var key = s[0];
                var kindNum = s.substring(1).split('.');
                try {
                    return that.skin[key][kindNum[0]][kindNum[1]];
                } catch (e) {
                    throw new Error("Cannot getVar: " + s + "\n" +
                                    JSON.stringify(that));
                }
            }
            function stringify(sexp) {
                if (sexp.shift) {
                    var args = sexp.slice(1).map(stringify);
                    args.unshift(that.meat.terms[sexp[0]]);
                    return "(" + args.join(" ") + ")";
                } else {
                    return getVar(sexp);
                }
            }
            var out = "";
            out += this.tree.cmd
            out += " ";
            out += "(" + this.skin.name;
            out += "\n  ";

            if (typeof this.tree.dkind === 'number') {
                out += this.meat.kinds[this.tree.dkind];
                out += " ";
                out += stringify(this.tree.dsig);
                out += "\n";
            }
            
            out += '(' + this.bone.free.map(function(fv) {
                return '(' + fv.map(getVar).join(' ') + ')';
            }).join(' ') + ')';
            out += "\n  ";
            out += "(";

            for (var i = 0; i < this.bone.hyps.length; i++) {
                if (this.tree.cmd != 'stmt') {
                    out += this.skin.hypNames[i];
                    out += " ";
                }
                out += stringify(this.bone.hyps[i]);
                if (i + 1 < this.bone.hyps.length) {
                    out += "\n   ";
                }
            }
            out += ")";
            out += "\n  ";

            out += stringify(this.bone.stmt);
            out += "\n  ";

            if (this.tree.proof) {
                function step(s) {
                    if (s.shift) {
                        return stringify(s);
                    } else if (s.match(/^hyps/)) {
                        return that.skin.hypNames[s.substring(5)];
                    } else if (s.match(/^deps/)) {
                        var depNum = s.substring(5);
                        var depKey = that.tree.deps[depNum];
                        var depName = factsByKey[depKey].skin.name;
                        var origDep = that.skin.depNames[depNum];
                        if (depName != origDep) {
                            console.log("Warning: using " + depName +
                                        " instead of " + origDep);
                        }
                        return depName;
                    } else {
                        var varName = getVar(s);
                        if (!varName) {
                            throw new Exception("bad proof step " + s);
                        }
                        return varName;
                    }
                }
                out += this.tree.proof.map(step).join(' ');
                out += "\n)\n";
            }
            return out;
        },
        getKey: function() {
            return JSON.stringify([this.bone, this.meat]);
        }
    };
    return obj;
}