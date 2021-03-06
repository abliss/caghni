(function(module) {
    var Path = require('path');
    var Fs = require('fs');
    var Fact = require('./fact.js');
    
    require('./sexpression.js')
    require('./typeset.js')
    require('./proofstep.js')
    require('./verify.js')

    // A subclass of the VerifyCtx which converts incoming proofs into caghni-space
    // and emits them to the given writer.
    function ConvertVerifyCtx(urlCtx, factCallback) {
        this.urlctx = urlCtx;
        this.factCallback = factCallback;
        this.factsByLabel = {};
        this.run = function(urlContext, url, context) {
            context.runUrl = url;
            var scanner = new GH.Scanner(urlContext.resolve(url).split(/\r?\n/));
            var command = GH.read_sexp(scanner);
            while (command) {
                // We don't care about styling, but apparently we need to
                // participate in passing it around.
                var styling = scanner.styleScanner.get_styling();
                styling.filename = ''; // WTF
                var arg = GH.read_sexp(scanner);
                context.do_cmd(command, arg, styling);
                scanner.styleScanner.clear();
                command = GH.read_sexp(scanner);
            }
        }
        GH.VerifyCtx.call(this, urlCtx, this.run);
        var exportedInterfaces = {};
        var thmRenameMap = {};
        // Creates, stores, and returns a new name for the theorem
        this.renameTheorem = function(origName, fv, hyps, stmt) {
            var name = JSON.stringify([fv, hyps, stmt]);
            thmRenameMap[origName] = name;
            return name;
        }
        // Returns the old name if we have not changed it
        // hypList: a list of tokens to avoid renaming
        this.getNewName = function(origName, hypList) {
            var name = thmRenameMap[origName];
            return name ? name : origName
        }
        // exported interface -> {origThmName -> newThmName}
        this.getRenameMap = function() {
            // TODO: clone for saftey.
            return exportedInterfaces;
        }
        this.exportInterface = function(inter) {
            // TODO: clone for saftey.
            exportedInterfaces[inter] = thmRenameMap;
        }
        // Get the num'th normalized var-name for the given kind.
        this.getVarName = function(kind, cmd, num) {
            var name = this.get_kind(kind);
            name += '.';
            if (cmd == 'tvar') name += "t";
            name += num;
            return name;
        }
    }

    ConvertVerifyCtx.prototype = new GH.VerifyCtx();
    ConvertVerifyCtx.prototype.constructor = ConvertVerifyCtx;

    ConvertVerifyCtx.prototype.do_cmd = function(cmd, arg, styling) {
        if (('thm' == cmd) || ('defthm' == cmd)) {
            // handled elsewhere
        } else if (('var' == cmd) || ('tvar' == cmd)) {
            // vars renamed based on kind
            // TODO: currently assuming only one var/tvar per kind
            var newArg = arg.slice();
            /* XXX
               var kind = arg[0];
               for (var i = 0; i + 1 < newArg.length; i++) {
               newArg[i + 1] = this.getVarName(kind, cmd, i);
               }
            */
        } else {
            // others copied verbatim
            if ('export' == cmd) {
                // TODO: clean out old ones, provide means for accessing unexported
                this.exportInterface(arg[1]);
            }
        }
        GH.VerifyCtx.prototype.do_cmd.apply(this, arguments);
    };


    // Maps tokens to sequential IDs starting at 0
    function Map() {
        var obj = {};
        var keys = [];
        this.put = function(tok) {
            if (obj.hasOwnProperty(tok)) {
                return obj[tok];
            }
            var id = keys.length;
            obj[tok] = id;
            keys.push(tok);
            return id;
        };
        this.has = function(tok) {
            return obj.hasOwnProperty(tok);
        };
        this.toJSON = function() {
            return JSON.stringify(keys);
        }
    }

    // Maintains named Maps for tokens
    function Style() {
        var maps = {};
        this.map = function(typ) {
            return maps.hasOwnProperty(typ) ? maps[typ] : (maps[typ] = new Map());
        }
        this.toJSON = function() {
            return JSON.stringify(maps);
        }
    }

    ConvertVerifyCtx.prototype.populateFact = function(fact, fv, hyps, stmt, proof,
                                                       dkind, dsig, syms) {
        var that = this;

        // Given a sexp, return the same sexp with each leaf that is a symbol
        // renamed according to the current fact.
        function symMapSexp(sexp) {
            if (GH.typeOf(sexp) != 'string') {
                return sexp.map(symMapSexp);
            }
            var sym = syms[sexp];
            if (!sym) {
                // it's not a sym, don't touch it
                return sexp;
            }
            var cmd = sym[0];
            switch(cmd) {
            case 'var':
            case 'tvar':
                var kind = sym[1];
                return fact.nameVar(sexp);
            case 'thm':
            case 'defthm':
            case 'stmt':
                var depFact = that.factsByLabel[sexp];
                var depName = fact.nameDep(sexp, depFact);
                if (!depFact) throw new Error("unknown dep " + sexp);
                return depName;
            default:
                throw new Error("Unknown symbol cmd " + cmd + " " + sexp);
            }
        }
        
        function getFreeMap(termList) {
            var out = [];
            termList[2].forEach(function(argSpec, argNum) {
                if (argSpec == null) {
                    return;
                };
                out[argNum] = argSpec.slice();
                out[argNum].sort();
            });
            return out;
        }
        
        // Like symMapSexp, but tries to map the first element of each sexp as an
        // operator.
        function mapSexp(sexp) {
            if (GH.typeOf(sexp) == 'string') {
                return symMapSexp(sexp);
            }
            var term = sexp[0];
            if (that.terms.hasOwnProperty(term) ||
                (dsig && (dsig[0] === term))) {
                term = fact.nameTerm(term, getFreeMap(that.terms[term]))
                // TODO: need to name tree term separately from bone/meat terms.
                // otherwise key gets dummy terms; see bicom
            }
            var out = sexp.slice(1).map(mapSexp);
            out.unshift(term);
            return out;
        }

        fact.setStmt(mapSexp(stmt));

        // Rename hypotheses to hyps.$hypNum
        var hypMap = {};
        var newHyps = [];
        for (var i = 0; i < hyps.length; i ++) {
            if (proof) { // stmts don't name hyps
                var hypName = hyps[i++];
                hypMap[hypName] = fact.nameHyp(hypName);
            }
            
            newHyps.push(mapSexp(hyps[i]));
        }
        fact.setHyps(newHyps);
        fact.setFree(symMapSexp(fv));

        function mapProofStep(step) {
            if (GH.typeOf(step) == 'string') {
                // TODO: check the ordering here. Namespaces overlap.
                if (hypMap.hasOwnProperty(step)) {
                    return hypMap[step];
                } else {
                    return symMapSexp(step);
                }
            } else {
                return mapSexp(step);
            }
        }

        if (proof) {
            fact.setProof(proof.map(mapProofStep));
        }

        // Look up and record the FreeMap for each term used in this fact.
        fact.FreeMaps = [];
        fact.Skin.TermNames.forEach(function(name, termNum) {
            var term = that.terms[name];
            fact.FreeMaps[termNum] = getFreeMap(term);
            if (dsig && (dsig[0] == name)) { // defthms
                fact.setDefiniendum(termNum);
            }

        });
    };
    ConvertVerifyCtx.prototype.add_assertion = function(kw, label, fv, hyps, concl,
                                                        varlist, num_hypvars, num_nondummies, syms, styling) {
        var proof, dkind, dsig;
        var myHyps = hyps, myKw = kw;
        if (this.lastProofChecked) {
            proof = this.lastProofChecked.proof;
            dkind = this.lastProofChecked.dkind;
            dsig = this.lastProofChecked.dsig;
            if (dkind) {
                myKw = 'defthm';
            }
            myHyps = this.lastProofChecked.hyps;
            delete this.lastProofChecked;
        }
        var fact = new Fact().setCmd(myKw).setName(label);
        this.populateFact(fact, fv, myHyps, concl, proof, dkind, dsig, syms);
        this.factsByLabel[label] = fact;
        this.factCallback(fact);
        var fact2;
        try {
            var verified = fact.verify();
            // Verify again after roundtripping to text
            fact2 = new Fact(JSON.parse(JSON.stringify(fact)));
            fact2.verify();
        } catch(e) {
            console.log("Error verifying " + JSON.stringify(fact), e);
            e.fact = fact;
            Fs.writeFileSync(fact.Skin.Name+".verify_fail.json",
                         JSON.stringify(fact));
            Fs.writeFileSync(fact.Skin.Name+"2.verify_fail.json",
                         JSON.stringify(fact2));
            //throw e;
        }
        // super()
        GH.VerifyCtx.prototype.add_assertion.apply(this, arguments);

    }

    ConvertVerifyCtx.prototype.check_proof = function(proofctx,
                                                      label, fv, hyps, stmt, proof,
                                                      dkind, dsig) {
        // Stash these since they are not available from add_assertion
        this.lastProofChecked = {
            proof: proof,
            dkind: dkind,
            dsig: dsig,
            hyps: hyps,
        };

        // super()
        GH.VerifyCtx.prototype.check_proof.apply(this, arguments);
    };

    ConvertVerifyCtx.prototype.get_export_ctx = function(prefix, pifs) {
        return new ConvertExportCtx(this, prefix, pifs);
    };

    // A subclass of GH.ExportCtx which converts exported stmts according to the
    // given map.
    function ConvertExportCtx(verify, prefix, params, writer, renameMap) {
        GH.InterfaceCtx.call(this, verify, prefix, params);
        this.assertions = {};
    };

    ConvertExportCtx.prototype = new GH.ExportCtx();
    ConvertExportCtx.prototype.constructor = ConvertExportCtx;

    ConvertExportCtx.prototype.do_cmd = function(cmd, arg, styling) {
        var newArg = arg.slice();
        if (cmd == 'stmt') {
            newArg[0] = this.verify.getNewName(arg[0]);
        }
        // super
        GH.ExportCtx.prototype.do_cmd.apply(this, arguments);
    }


    module.exports = ConvertVerifyCtx;
})(module)
