#!/usr/bin/node
/**
 * Convert.js
 * Usage: ./convert.js indir
 * Blows away directory out-v${version}, and fills it with the objects parsed
 * from the indir.
 */

var VERSION = 2;
/**
 * Version 2: Builds a LevelDB of all content (see README.md for
 * schema). Capable of recreating the inputs byte-for-byte; also capable of
 * translating a thm (with proof) from one ghilbert corpus to another.
 */

var Process = process;
var Path = require('path');
var Fs = require('fs');
var Rimraf = require('rimraf');
var Fact = require('./fact.js');

GH = global.GH = {};
global.log = console.log;
require('./verify.js')
require('./proofstep.js')

var args = Process.argv;

var outDir = "out-v" + VERSION;
if (args.length != 3) {
    console.log("Usage: ./convert.js indir");
    console.log("Blows away " + outDir);
    process.exit(-1);
}

Rimraf.sync(outDir);
Fs.mkdirSync(outDir);

var inDir = Process.argv[2];



function NodeUrlContext(rootDir) {
    this.resolve = function(url) {
        // TODO(abliss): sometimes the path has repeats?
        var path = Path.join(rootDir, url);
        path = path.replace(/peano\/peano\//, 'peano/');
        return Fs.readFileSync(path).toString();
    };
}


// A subclass of the VerifyCtx which converts incoming proofs into caghni-space
// and emits them to the given writer.
function ConvertVerifyCtx(urlCtx) {
    this.urlctx = urlCtx;
    this.factsByLabel = {};
    this.factsByKey = {};
    var ghText = "";
    this.write = function(str) { ghText += str; };
    this.getGhText = function() { return ghText; }
    this.run = function(urlContext, url, context) {
        context.runUrl = url;
        var scanner = new GH.Scanner(urlContext.resolve(url).split(/\r?\n/));
        var command = GH.read_sexp(scanner);
        while (command) {
            // We don't care about styling, but apparently we need to
            // participate in passing it around.
            var styling = scanner.styleScanner.get_styling();
            var arg = GH.read_sexp(scanner);
            context.do_cmd(command, arg, styling);
            scanner.styleScanner.clear();
            command = GH.read_sexp(scanner);
        }
    }

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
        this.write(cmd + " " + GH.sexp_to_string(newArg) + "\n");
    } else {
        // others copied verbatim
        if ('export' == cmd) {
            // TODO: clean out old ones, provide means for accessing unexported
            this.exportInterface(arg[1]);
        }
        this.write("    " + cmd + " " + GH.sexp_to_string(arg) + "\n");
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
           return fact.nameVar(cmd, kind, sexp);
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
    
    // Like symMapSexp, but tries to map the first element of each sexp as an
    // operator.
    function mapSexp(sexp) {
        if (GH.typeOf(sexp) == 'string') {
            return symMapSexp(sexp);
        }
        var term = sexp[0];
        if (that.terms.hasOwnProperty(term) ||
            (dsig && (dsig[0] === term))) {
            term = fact.nameTerm(term);
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

    if (dkind) { // defthms
        fact.setDkind(fact.nameKind(dkind));
        var newDsig = mapSexp(dsig);
        newDsig[0] = fact.nameTerm(dsig[0]);
        fact.setDsig(newDsig);
    }
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
    var fact = Fact().setCmd(myKw).setName(label);
    this.populateFact(fact, fv, myHyps, concl, proof, dkind, dsig, syms);
    if (proof) {
        this.write(fact.toGhilbert(this.factsByKey));
    }
    this.factsByLabel[label] = fact;
    this.factsByKey[fact.getKey()] = fact;
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

    var ghText = "";
    this.write = function(str) { ghText += str; };
    this.getGhText = function() { return ghText; }

};

ConvertExportCtx.prototype = new GH.ExportCtx();
ConvertExportCtx.prototype.constructor = ConvertExportCtx;

ConvertExportCtx.prototype.do_cmd = function(cmd, arg, styling) {
    var newArg = arg.slice();
    if (cmd == 'stmt') {
        newArg[0] = this.verify.getNewName(arg[0]);
    }
    this.write(cmd + " " + GH.sexp_to_string(newArg) + "\n");
    // super
    GH.ExportCtx.prototype.do_cmd.apply(this, arguments);
}



// TODO: for now assume each directory is a ghilbert module
function processGhilbertModule(moduleName) {
    // exported interface -> {oldThm -> newThm}
    var exportedInterfaces = {};
    function processProofFile(fileName) {
        if (fileName.match(/\.gh$/)) {
            var path = Path.join(outDir, moduleName, fileName);
            console.log("    XXXX Processing proof " + fileName);
            var verifyCtx = new ConvertVerifyCtx(urlCtx);
            verifyCtx.run(urlCtx, fileName, verifyCtx);
            Fs.writeFileSync(path, verifyCtx.getGhText());
            var map = verifyCtx.getRenameMap();
            Fs.writeFileSync(path + "_map", JSON.stringify(map));
            var ifaces = verifyCtx.interfaces;
            for (var iname in ifaces) if (ifaces.hasOwnProperty(iname)) {
                if (ifaces[iname].getGhText) {
                    console.log("    XXXX Exported! " + ifaces[iname].runUrl);
                    exportedInterfaces[ifaces[iname].runUrl] = ifaces[iname];
                }
            }
        }
    }
    function processInterfaceFile(fileName) {
        if (fileName.match(/\.ghi$/)) {
            // TODO: assumes / for path separator.
            var url = '/' + moduleName + '/' + fileName;
            console.log("    XXXX Processing interface " + url);
            var outText;
            if (exportedInterfaces[url]) {
                console.log("    XXXX Exported! " + url);
                outText = exportedInterfaces[url].getGhText();
            } else {
                outText = Fs.readFileSync(inDir + url);
            }
            Fs.writeFileSync(outDir + url, outText);
        }
    }
    Fs.mkdirSync(Path.join(outDir, moduleName));
    var urlCtx = new NodeUrlContext(Path.join(inDir, moduleName));

    var files = Fs.readdirSync(Path.join(inDir, moduleName));
    files.forEach(processProofFile);
    files.forEach(processInterfaceFile);

}

Fs.readdirSync(inDir).forEach(processGhilbertModule);
