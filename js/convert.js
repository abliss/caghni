#!/usr/bin/node
/**
 * Convert.js
 * Usage: ./convert.js indir outdir
 */

var VERSION = 4;
/**
 * Version 4: Builds a LevelDB of all content (see README.md for
 * schema). Numeric Core instead of stringy Meat.
 */

GH = global.GH = {};

var Process = process;
var Path = require('path');
var Fs = require('fs');
var Crypto = require('crypto');
var Fact = require('./fact.js');
var Converter = require('./converter.js');


global.log = console.log;
require('./sexpression.js')
require('./typeset.js')
require('./proofstep.js')
require('./verify.js')

var args = Process.argv;

if (args.length != 4) {
    console.log("Usage: ./convert.js gh-dir outdir");
    process.exit(-1);
}
var inDir = args[2];
var outDir = args[3];

try {
    Fs.mkdirSync(outDir);
} catch (e) {
    // ignore EEXIST
}

var Level = require('level');
var factsDb = Level(Path.join(outDir, 'facts.leveldb'));

function makeDbKey(fact) {
    var factJson = JSON.stringify(fact);
    var hash = Crypto.createHash('sha1');
    hash.update(factJson);
    var sha1 = hash.digest('hex');
    var key = fact.getKey() + ";" + sha1;
    
    return key;
}


function NodeUrlContext(rootDir) {
    this.resolve = function(url) {
        // TODO(abliss): sometimes the path has repeats?
        var path = Path.join(rootDir, url);
        path = path.replace(/peano\/peano\//, 'peano/');
        return Fs.readFileSync(path).toString();
    };
}


// TODO: for now assume each directory is a ghilbert module
function processGhilbertModule(moduleName) {
    // exported interface -> {oldThm -> newThm}
    var exportedInterfaces = {};
    function processProofFile(fileName) {
        if (fileName.match(/\.gh$/)) {
            var path = Path.join(outDir, moduleName, fileName);
            console.log("    XXXX Processing proof " + fileName);
            var verifyCtx = new Converter(
                urlCtx, function(fact) {
                    factsDb.put(makeDbKey(fact), JSON.stringify(fact));
                });
            verifyCtx.run(urlCtx, fileName, verifyCtx);
            var map = verifyCtx.getRenameMap();
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
        }
    }
    var urlCtx = new NodeUrlContext(Path.join(inDir, moduleName));
    var files = Fs.readdirSync(Path.join(inDir, moduleName));
    files.forEach(processProofFile);
    files.forEach(processInterfaceFile);
}


Fs.readdirSync(inDir).forEach(processGhilbertModule);
factsDb.close()
