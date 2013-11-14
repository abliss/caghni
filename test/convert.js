#!/usr/bin/node
/**
 * Convert.js
 * Usage: ./convert.js indir
 * Blows away directory out-v${version}, and fills it with the objects parsed
 * from the indir.
 */

var VERSION = 1;

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
}

ConvertVerifyCtx.prototype = new GH.VerifyCtx();
ConvertVerifyCtx.prototype.constructor = ConvertVerifyCtx;

ConvertVerifyCtx.prototype.do_cmd = function(cmd, arg, styling) {
    if (('thm' == cmd) || ('defthm' == cmd)) {
        // [def]thm commands are written in check_proof; others copied verbatim
    } else {
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
    var thmSexp = [];
    if (dkind) { // defthms
        thmSexp.push(this.renameTheorem(label, fv, hyps, stmt), dkind, dsig);
        this.write("defthm ");
    } else {
        thmSexp.push(this.renameTheorem(label, fv, hyps, stmt));
        this.write("thm ");
    }

    // We must not rename hypotheses, even if they are also thm names
    var hypsMap = {};
    hyps.forEach(function(hyp) { hypsMap[hyp] = 1; });
    var that = this;
    var newProof = proof.map(function(step) {
        return hypsMap[step] ? step : that.getNewName(step);
    });

    thmSexp.push(fv, hyps, stmt);
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
