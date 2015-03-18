#!/usr/bin/node
/**
 * Convert.js
 * Usage: ./convert.js indir outdir
 */

var VERSION = 5;
/**
 * Version 5: Pretty-prints to the filesystem. See README.md for schema.
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
var useLevel = false;

try {
    Fs.mkdirSync(outDir);
} catch (e) {
    // ignore EEXIST
}

var factsDb;

if (useLevel) {
    var Level = require('level');
    factsDb = Level(Path.join(outDir, 'facts.leveldb'));
} else {
    factsDb = {
        put: function(key, value) {
            var filename = key;
            filename = encodeURIComponent(filename);
            filename = filename.replace(/%5B/g,'C'); // [
            filename = filename.replace(/%5D/g,'D'); // ]
            filename = filename.replace(/%2C/g,'.'); // ,
            filename = filename.replace(/%3B/g,'/'); // ;
            filename = filename.split(/\//g).map(function(x) {
                // split up path components that are too long
                return x.replace(/(.{250})/g,"$1_/_");
            }).join("/");
            var path  = filename.split(/\//g);
            for (var i = 0; i < path.length; i++) {
                try {
                    Fs.mkdirSync(outDir + "/" + path.slice(0,i).join('/'));
                } catch(e) {
                    // ignore EEXIST
                }
            }
            Fs.writeFileSync(outDir + "/" + filename, value);
        },
        close: function(){
        },
    }
}

function makeDbKey(fact) {
    var factJson = JSON.stringify(fact); // TODO: canonicalize
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


// Like JSON.stringify, but prettier.
function prettyPrint(depth, obj) {
    return JSON.stringify(obj, null, "  ")
        .replace(/\[\s+/g,'[')
        .replace(/\s+]/g,']')
        .replace(/\s+([0-9])/g,"$1")
        .replace(/\s+("[^"]+"[^:])/g,'$1');
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
                    var pretty = prettyPrint(0, fact);
                    factsDb.put(makeDbKey(fact), pretty);
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
