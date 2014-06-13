#!/usr/bin/node
/**
 * query.js
 * Usage: ./query.js dbDir>
 */

var Fact = require('./fact.js');
var Level = require('level');
var Path = require('path');
var Process = process;
var Fs = require('fs');


var args = Process.argv;
var outDir = args[2];
var factsDb = Level(Path.join(outDir, 'facts.leveldb'));

// Welcome to callback HELL! Muhuhahaha. Ha.

function score(fact, hint) {
    var n = 0; 
    if (fact.Skin.Name == hint.name) {
        n += 10;
    }
    if ((fact.Tree.Cmd == "stmt") === (hint.name.match(/^ax-/) ? true : false)) {
        n += 1;
    }
    if (context.axiomTerms[fact.getNewTerm()]) {
        n -= 100;
    }

    return n;
}

// Infer term arities. TODO: should be more strict here.
function inferTerms(fact) {
    function recurse(exp) {
        if (exp.slice) {
            var termName = fact.Skin.TermNames[exp[0]];
            if (!context.iface.terms[termName]) {
                var t = "term (k (" + termName;
                var arity = exp.length - 1;
                for (var k in context.iface.vars) {
                    if (context.iface.vars.hasOwnProperty(k)) {
                        if (arity == 0) {
                            break;
                        }
                        t += " " + k;
                        arity--;
                    }            
                }
                t += "))\n";
                context.iface.terms[termName] = t;
            }
            exp.slice(1).forEach(recurse);
        }
    }
    recurse(fact.Core[Fact.CORE_STMT]);
}

var context = {};
context.pendingTheorems = {};
context.axiomTerms = {"-.": 1, "->": 1}; //XXX
context.requestFact = function(core, hint, cb) {
    // TODO: keying this by hint.name assumes no two different facts have the
    // same name.
    var oldHit = context.map[hint.name];
    if (oldHit) {
        //console.log("Requeried " + hint.name);
        // move to front of dll if it's not there already.
        if ((oldHit.node) && (oldHit.node !== context.proofs.dll)) {
            var p = oldHit.node.prev;
            var q = oldHit.node.next;
            if (p) {
                p.next = q;
            }
            if (q) {
                q.prev = p;
            }
            oldHit.node.prev = null;
            var oldHead = context.proofs.dll;
            oldHit.node.next = oldHead;
            oldHead.prev = oldHit.node;
            context.proofs.dll = oldHit.node;
            // we need to pull all of its dependencies to the front.
            // TODO: The following is an easy, but stupidly-slow way.
            oldHit.fact.toGhilbert(context, function(err, out) {
                if (err) {
                    err += "\n  Moving to front: " + oldHit.fact.Skin.Name;
                    cb(err, null);
                }
            });
        }
        cb(null, oldHit.fact);
        return;
    }
    var opts = {start:JSON.stringify(core) + ";"};
    opts.end = opts.start + "\xff";
    var best;
    factsDb.createReadStream(opts).
        on('error', function(err) {
            err += "\n  Reading DB for " + hint;
            cb(err, null);
        }).
        on('close', function() {
            /*
            cb("Closed!\n  Query=" + JSON.stringify(opts) +
               "\n  Best=" + JSON.stringify(best), null);
            */
        }).
        on('data', function(data) {
            // Avoid loops
            var fact = new Fact(JSON.parse(data.value));
            //console.log("Queried " + hint.name + " got " + fact.Skin.Name);
            if (!best || (score(fact, hint) > score(best.fact, hint))) {
                best = {key: data.key, fact: fact};
            }
        }).
        on('end', function() {
            if (best) {
                if (context.map[best.fact.Skin.Name]) { //XXX key
                    //console.log("# XXXX Already got it");
                    cb(null, best.fact);
                } else {
                    var newNode = {text:null,
                                   prev:null,
                                   next:null};
                    context.map[best.fact.Skin.Name] = {fact: best.fact};
                    context.pendingTheorems[best.key] = true;
                    var isThm = best.fact.Tree.Cmd !== 'stmt';
                    if (isThm) {
                        context.map[best.fact.Skin.Name].node = newNode;
                    }
                    var where = isThm ? context.proofs : context.iface;
                    // add vars (and terms?)
                    best.fact.Skin.VarNames.forEach(function(v) {
                        // TODO: kinds
                        // TODO: t/v
                        where.vars[v] = "tvar (k " + v + ")\n";
                        
                    });
                    if (!isThm) {
                        inferTerms(best.fact);
                    }
                    newNode.next = where.dll;
                    if (where.dll) {
                        where.dll.prev = newNode;
                    }
                    where.dll = newNode;
/*
                    console.log("# XXXX Getting ghilbert for " +
                                best.fact.Skin.Name +
                                " as " + best.fact.Tree.Cmd);
*/
                    best.fact.toGhilbert(context, function(err, out) {
                        if (err) {
                            err += "\n  Ghilbertizing " + best.fact.Skin.Name;
                            cb(err, null);
                        } else {
                            console.log("Finished with " + best.fact.Skin.Name + " = " + best.key);
                            context.pendingTheorems[best.key] = false;
                            newNode.text = out;
                            cb(null, best.fact);
                        }
                    });
                }
            } else {
                cb("Not found!\n  Query=" + JSON.stringify(hint), null);
            }
        });    
};

context.map = {};
context.proofs = {
    dll: null,
    vars:{},
}

context.iface = {
    dll: null,
    vars:{},
    terms: {},
}


function concatDll(node) {
    var out = "";
    var seen = {};
    while (node) {
        if (seen[node.text]) {
            throw new Error("List is cyclic! " + node.text +
                            "\n AFTER \n" + out);
        }
        seen[node.text] = true;
        out += node.text
        node = node.next;
    }
    return out;
}
function finish() {
    var str = "";
    str += "kind (k)\n"; // TODO: kind
    function appendVals(obj) {
        for (var k in obj) if (obj.hasOwnProperty(k)) {
            str += obj[k];
        }
    }
    appendVals(context.iface.vars);
    appendVals(context.iface.terms);
    str += concatDll(context.iface.dll);
    Fs.writeFileSync("tmp.ghi", str);

    str = "";
    str += 'import (TMP tmp.ghi () "")\n';
    appendVals(context.proofs.vars);
    str += concatDll(context.proofs.dll);
    Fs.writeFileSync("tmp.gh", str);
}

if (true) {
    factsDb.get(
        // "[[],[0,[0,0,1],[0,[0,1,2],[0,0,2]]],[]];add30c32799d8ec9a84c54adae34b3dbeb8e128a", //nic-luk1
        "[[],[0,[1,0,[1,1,[0,[2,[3,0,2],[3,1,3]],[4,0,1]]]],[5,4,[2,[1,1,[0,[2,[6,[7,[7,1]],5],[3,[7,[7,1]],2]],[8,[7,[7,1]],4]]],[1,1,[0,[3,[7,[7,1]],3],[9,[8,[7,[7,1]],4]]]]]]],[[2,0,1,4],[3,0,1,4],[5,1,4]]];13f6897af1da323d39c68b6f070ad5a14c72b4a0", // relprimex
                function(err, data) {
        if (err) {
            console.log(err);
        } else {
            var fact = new Fact(JSON.parse(data));
            var node = {
                text:null,
                next:null,
                prev:null
            }
            context.proofs.dll = node;
            context.map[fact.Skin.Name] = {fact:fact, node:node};
            fact.toGhilbert(context, function(err, out) {
                if (err) {
                    console.log("ERROR: " + err);
                    Process.exit(-1);
                } else {
                    node.text = out;
                    finish();
                }
            });
        }
    });

} else {
    var core = "[[],[0,[1,0,[1,1,[0,[2,";
    var opts = {start:core};
    opts.end = opts.start + "\xff";
    var best;
    factsDb.createReadStream(opts).
        on('data', function(data) {
            console.log(data)
        });

}