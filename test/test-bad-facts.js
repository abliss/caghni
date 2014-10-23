var Fact = require('../js/fact.js');
var Fs = require('fs');

var badFacts = eval(Fs.readFileSync('bad-facts/all.js', 'utf-8'));
badFacts.forEach(function(data) {
    var fact = new Fact(data);
    var verified = false;
    try {
        verified = fact.verify();
    } catch (e) {
        // expected
    }
    if (verified) {
        throw "Bad fact verified! " + JSON.stringify(fact);
    }
});
console.log("ok");
