#!/usr/bin/node
/**
 * fingerprint.js
 * Usage: ./fingerprint.js indir
 * crawls indir and computes the fingerprint of each interface we find.
 */

var VERSION = 'y';

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

if (args.length != 3) {
    console.log("Usage: ./fingerprint.js gh-dir");
    process.exit(-1);
}
var inDir = args[2];

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
    function processFile(fileName) {
        if (fileName.match(/\.gh$/)) {
            console.log("    XXXX Verifying proof " + fileName);
            var verifyCtx = new Converter(
                urlCtx, function(fact) {
                    //console.log(" Coverted fact: " + fact.Skin.Name);
                });
            verifyCtx.run(urlCtx, fileName, verifyCtx);
            var map = verifyCtx.getRenameMap();
            var ifaces = verifyCtx.interfaces;
            for (var iname in ifaces) if (ifaces.hasOwnProperty(iname)) {
                console.log("XXXX iface: " + iname);
                // PICKUP: determine import/export by proto?
                if (ifaces[iname].getGhText) {
                    console.log("    XXXX Exported! " + ifaces[iname].runUrl);
                    exportedInterfaces[ifaces[iname].runUrl] = ifaces[iname];
                }
            }

        } else if (fileName.match(/\.ghi$/)) {
            // TODO: assumes / for path separator.
            var url = '/' + moduleName + '/' + fileName;
            console.log("    XXXX Skipping interface " + url);
        }        
    }
    var urlCtx = new NodeUrlContext(Path.join(inDir, moduleName));
    var files = Fs.readdirSync(Path.join(inDir, moduleName));
    files.forEach(processFile);
}


Fs.readdirSync(inDir).forEach(processGhilbertModule);

