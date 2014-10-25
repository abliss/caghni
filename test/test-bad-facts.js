// Node script to test bad facts
var Fact = require('../js/fact.js');
var Fs = require('fs');
var Path = require('path');

var count = 0;
Fs.readdirSync("bad-facts").forEach(function(filename) {
    var data = eval('(' + 
                    Fs.readFileSync('bad-facts/' + filename, 'utf-8')
                   + ')');
    var fact = new Fact(data);
    var verified = false;
    try {
        verified = fact.verify();
    } catch (e) {
        // expected
        count++;
    }
    if (verified) {
        throw "Bad fact verified! " + JSON.stringify(fact);
    }
});
console.log("Bad facts failed to verify: " + count);
console.log("ok");
