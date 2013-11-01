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

var args = Process.argv;

var outDir = "out-v" + VERSION;
if (args.length != 3) {
    console.log("Usage: ./convert.js indir");
    console.log("Blows away " + outDir);

}

Rimraf.sync(outDir);
Fs.mkdirSync(outDir);

var inDir = Process.argv[2];
Fs.readdirSync(inDir).forEach(processGhilbertModule);

// TODO: for now assume each directory is a ghilbert module
function processGhilbertModule(moduleName) {
    Fs.mkdirSync(Path.join(outDir, moduleName));
    Fs.readdirSync(Path.join(inDir, moduleName)).forEach(processGhilbertFile);
    function processGhilbertFile(fileName) {
        var blob = Fs.readFileSync(Path.join(inDir, moduleName, fileName)).toString();
        console.log("File " + fileName + " size " + blob.length);
        Fs.writeFileSync(Path.join(outDir, moduleName, fileName), blob);
    }
}
