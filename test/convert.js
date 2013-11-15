#!/usr/bin/node
/**
 * Convert.js
 * Usage: ./convert.js indir
 * Blows away directory out-v${version}, and fills it with the objects parsed
 * from the indir.
 */

var VERSION = 1;
/**
 * Version 1:
 * - all thms and defthms are renamed to the JSON.stringify of their
 *   sexps (including dvs and hyps).
 * - Hypotheses are changed to hyp0, hyp1, ....
 * - variables are changed to kind.[t]0, kind.[t]1, ... (not in interfaces)R
 * - Exported interfaces are updated; Imported interfaces are not.
 */

var Process = process;
var Path = require('path');
var Fs = require('fs');
var Rimraf = require('rimraf');

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
        // [def]thm commands are written in check_proof;
    } else if (('var' == cmd) || ('tvar' == cmd)) {
        // vars renamed based on kind
        // TODO: currently assuming only one var/tvar per kind
        var newArg = arg.slice();
        var kind = arg[0];
        for (var i = 0; i + 1 < newArg.length; i++) {
            newArg[i + 1] = this.getVarName(kind, cmd, i);
        }
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

ConvertVerifyCtx.prototype.check_proof = function(proofctx,
                                                  label, fv, hyps, stmt, proof,
                                                  dkind, dsig) {
    // Rename hypotheses to h0,h1,...,hn
    var hypsMap = {};
    var newHyps = hyps.slice();
    for (var i = 0; i < hyps.length / 2; i++) {
        var newName = "h" + i;
        hypsMap[hyps[2 * i]] = newName;
        newHyps[2 * i] = newName;
    }
    var that = this;
    var newProof = proof.map(function(step) {
        var newName = hypsMap[step];
        if (!newName) newName = that.getNewName(step);
        return newName;
    });

    // Rename variables to kind.[t]0, kind.[t]1, ...
    var varsMap = {};
    var kindToVarNum = {}
    // Returns a new sexp with each of the var terms renamed.
    function varMapSexp(sexp) {
        if (GH.typeOf(sexp) == 'string') {
            var name = varsMap[sexp];
            if (name) return name;
            var sym = that.syms[sexp];
            if (sym && (sym[0] == 'var' || sym[0] == 'tvar')) {
                var cmd = sym[0];
                var kind = sym[1];
                var num = kindToVarNum[kind + cmd] || 0;
                name = that.getVarName(kind, cmd, num);
                kindToVarNum[kind + cmd] = num + 1;
                varsMap[sexp] = name;
                return name;
            } else {
                // it's not a var, don't touch it
                if (("" + sexp).match(/null/)) {
                    throw new Error("XXXX wtf? " + sexp);
                }
                return sexp;
            }
        } else {
            return sexp.map(varMapSexp);
        }
    }
    // Like varMapSexp, but skips the first element in each sexp since it is a
    // term, and terms can unfortunately have the same name as variables (e.g. S
    // and T)
    function varMapTerm(term) {
        if (GH.typeOf(term) == 'string') {
            return varMapSexp(term);
        } else {
            var out = term.slice(1).map(varMapTerm);
            out.unshift(term[0]);
            return out;
        }
    }
    for (var i = 1; i < hyps.length; i+= 2) {
        newHyps[i] = varMapTerm(hyps[i]);
    }

    var newStmt = varMapTerm(stmt);
    var newFv = varMapSexp(fv);

    newProof.unshift("  "); // so we can safely use varMapTerm
    newProof = varMapTerm(newProof);
    // Rename thm label to sexp json
    var thmSexp = [];
    this.write("# Was: " + label + "\n");
    if (dkind) { // defthms
        newDsig = varMapSexp(dsig);
        thmSexp.push(this.renameTheorem(label, newFv, newHyps, newStmt),
                     dkind, newDsig);
        this.write("defthm ");
    } else {
        thmSexp.push(this.renameTheorem(label, newFv, newHyps, newStmt));
        this.write("thm ");
    }

    thmSexp.push(newFv, newHyps, newStmt);
    thmSexp.push.apply(thmSexp, newProof);
    this.write(GH.sexp_to_string(thmSexp) + "\n");

    // super
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
    GH.ExportCtx.prototype.do_cmd.apply(this, arguments);

    // super

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
