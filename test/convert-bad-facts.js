// Node script to populate the bad-facts directory from a ghilbert test suite
// run with `node ./convert-bad-facts.js ../ghilbert/testsuite`
GH = global.GH = {};
var Fact = require('../js/fact.js');
var Fs = require('fs');
var Converter = require('../js/converter.js');

var count = 0;
var counts = {};
GH.DefaultCtx = function(urlctx, run) {
    var converter = new Converter(urlctx, function(fact) {
        try {
            fact.verify();
        } catch (e) {
            fact.Skin.Name = e.message;
            var filename = e.message.replace(/[^a-zA-Z0-9]/g, '_');
            var num = counts[filename] | 0;
            counts[filename] = num + 1;
            if (num) {
                filename += "-" + num;
            }
            Fs.writeFileSync('bad-facts/' + filename + ".js",
                             JSON.stringify(fact));
            count++;
            throw e;
        }
    });
    converter.suppress_errors = true;
    return converter;
}

try {
    require('../ghilbert/js/verify_test.js')
} catch (e) {
    console.log("verify_test error: " + e);
}
console.log("Bad facts converted: " + count);
console.log("ok");

