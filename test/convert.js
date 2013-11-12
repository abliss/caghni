#!/usr/bin/node
/**
 * Convert.js
 * Usage: ./convert.js indir
 * Blows away directory out-v${version}, and fills it with the objects parsed
 * from the indir.
 */

var VERSION = 0;

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


function run(urlContext, url, context) {
  var scanner = new GH.Scanner(urlContext.resolve(url).split(/\r?\n/));
  while (true) {
    var command = GH.read_sexp(scanner);
    if (command === null || command === undefined) {
      return true;
    }
    if (GH.typeOf(command) != 'string') {
      throw 'Command must be atom';
    }
    // We don't care about styling, but apparently we need to participate in passing
    // it around.
    var styling = scanner.styleScanner.get_styling();
    var arg = GH.read_sexp(scanner);
    context.do_cmd(command, arg, styling);
    scanner.styleScanner.clear();
  }
  return false;
}



// A subclass of the VerifyCtx which converts incoming proofs into caghni-space
// and emits them to the given writer.
function ConvertVerifyCtx(urlCtx, run, writer) {
    this.urlctx = urlCtx;
    this.run = run;
    this.writer = writer;
}

ConvertVerifyCtx.prototype = new GH.VerifyCtx();
ConvertVerifyCtx.prototype.constructor = ConvertVerifyCtx;

ConvertVerifyCtx.prototype.do_cmd = function(cmd, arg, styling) {
    if ('thm' !== cmd) {
        // thm commands are written in check_proof; all others copied verbatim
        this.writer.write("    " + cmd + " " + GH.sexp_to_string(arg) + "\n");
    }
    GH.VerifyCtx.prototype.do_cmd.apply(this, arguments);
};

ConvertVerifyCtx.prototype.check_proof = function(proofctx,
                                                  label, fv, hyps, stmt, proof,
                                                  dkind, dsig) {
    if (!dkind) { // defthms handled elsewhere
        var thmSexp = [label, fv, hyps];
        thmSexp.push(stmt);
        thmSexp.push.apply(thmSexp, proof);
        this.writer.write("thm " + GH.sexp_to_string(thmSexp) + "\n");
    }
    GH.VerifyCtx.prototype.check_proof.apply(this, arguments);
};



// TODO: for now assume each directory is a ghilbert module
function processGhilbertModule(moduleName) {
    Fs.mkdirSync(Path.join(outDir, moduleName));
    var urlCtx = new NodeUrlContext(Path.join(inDir, moduleName));
    
    Fs.readdirSync(Path.join(inDir, moduleName)).forEach(processGhilbertFile);
    function processGhilbertFile(fileName) {
        //verifyCtx.add_sym_hint = console.log;
        var out = Fs.createWriteStream(Path.join(outDir, moduleName, fileName));
        if (fileName.match(/\.gh$/)) {
            console.log("    XXXX Processing " + fileName);
            var verifyCtx = new ConvertVerifyCtx(urlCtx, run, out);
            run(urlCtx, fileName, verifyCtx);
        } else {
            // interface files just copied for now
            out.write(Fs.readFileSync(Path.join(inDir, moduleName, fileName)));
        }
    }
}

Fs.readdirSync(inDir).forEach(processGhilbertModule);
