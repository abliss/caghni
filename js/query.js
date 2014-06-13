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
    if (JSON.stringify(fact.Skin.TermNames) ===
        JSON.stringify(hint.terms)) {
        n += 1000;
    }
    return n;
}

// Tool for inferring term declarations.
// Each term declaration will have its own set of variabled declared.
// If the ith input to a term is *ever* another term, we declare it as termvar.
// If it is never a term but always a variable, we declare it as a binding var.
function InferredTerm(name, arity) {
    this.name = name;
    this.arity = arity;
    this.isTerm = [];
    this.isBinding = [];
    this.kind = "k"; // TODO:kinds
}
InferredTerm.prototype.toString = function() {
    var v = "\n";
    var t = "term (" + this.kind + " (" + this.name;
    for (var i = 0; i < this.arity; i++) {
        var varName = this.name + "_" + i;
        v += this.isTerm[i] ? "tvar" : " var";
        v += " (k "; // TODO: kinds
        v += varName;
        v += ")\n";
        t += " " + varName;
    }
    t += "))\n";
    return v + t;
}
function inferTerms(fact) {
    var bindingVars = {};
    // Collect binding vars from the fact's Free clause.
    fact.Core[Fact.CORE_FREE].forEach(function(free) {
        //In free variable constraint context clause, the first variable must be
        //a term variable and the remaining variables must be binding variables.
        free.slice(1).forEach(function(bv) {
            bindingVars[fact.Skin.VarNames[bv]] = 1;
        });
        // TODO: there is a possible problem here if one Fact considers a var
        // binding and another considers it term:
        // Collision of separately-defined vars.
        
    });
    function recurse(exp) {
        if (!Array.isArray(exp)) {
            return;
        }
        var termName = fact.Skin.TermNames[exp[0]];
        if (!termName) {
            throw new Error("Bad term " + exp[0] + " : " +
                            JSON.stringify(fact));
        }
        var it = context.terms[termName];
        if (!it) {
            it = new InferredTerm();
            it.name = termName;
            context.terms[termName] = it;
        }
        if (fact.Tree.Cmd == 'stmt') {
            context.axiomTerms[termName] = it;
        }
        var arity = exp.length - 1;
        if (isNaN(it.arity)) {
            it.arity = arity;
        } else {
            if (it.arity != arity) {
                // TODO: more graceful handling
                throw new Error("Arity mismatch! Term " + termName +
                                " was " + it.arity + " now " + arity);
            }
        }
        for (var i = 0; i < arity; i++) {
            var arg = exp[i+1];
            if (Array.isArray(arg)) {
                if (it.isBinding[i]) {
                    // Collision of separately-defined terms.
                    throw new Error("Houston, we have a problem." +
                                    "\nterm=" + termName +
                                    "\ni=" + i +
                                    "\nfact=" + JSON.stringify(fact));
                }
                it.isTerm[i] = true;
                recurse(arg);
            } else {
                var v = fact.Skin.VarNames[arg];
                if (!v) {
                    throw new Error("Bad VarName " + arg + " i=" + i +
                                    " exp=" + JSON.stringify(exp) +
                                    " fact=" + 
                                    JSON.stringify(fact));
                }
                if (bindingVars[v] || it.isBinding[i]) {
                    context.vars[v] = " var (k " + v + ")\n"; // TODO: kinds
                } else if (!context.vars[v]) {
                    context.vars[v] = "tvar (k " + v + ")\n"; // TODO: kinds
                }
            }
        }
    }
    recurse(fact.Core[Fact.CORE_STMT]);
}

var context = {};
context.pendingTheorems = {};
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
                    inferTerms(best.fact);
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
}
context.vars = {};
context.terms = {};
context.axiomTerms = {};
context.iface = {
    dll: null,
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
    appendVals(context.vars);
    appendVals(context.axiomTerms);
    str += concatDll(context.iface.dll);
    Fs.writeFileSync("tmp.ghi", str);

    str = "";
    str += 'import (TMP tmp.ghi () "")\n';
    appendVals(context.vars);
    str += concatDll(context.proofs.dll);
    Fs.writeFileSync("tmp.gh", str);
}

if (true) {
    factsDb.get(
        // "[[],[0,[0,0,1],[0,[0,1,2],[0,0,2]]],[]];add30c32799d8ec9a84c54adae34b3dbeb8e128a", //nic-luk1
        // "[[],[0,[1,0,[1,1,[0,[2,[3,0,2],[3,1,3]],[4,0,1]]]],[5,4,[2,[1,1,[0,[2,[6,[7,[7,1]],5],[3,[7,[7,1]],2]],[8,[7,[7,1]],4]]],[1,1,[0,[3,[7,[7,1]],3],[9,[8,[7,[7,1]],4]]]]]]],[[2,0,1,4],[3,0,1,4],[5,1,4]]];13f6897af1da323d39c68b6f070ad5a14c72b4a0", // relprimex
        '[[],[0,[1,0,1],[1,1,0]],[]];a3d0702f50d44f57e382db0b977c52e3df6c2a50', //addcom
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
    var core = "[[],[0,[1,0,1],[1,1,0]";
    var opts = {start:core};
    opts.end = opts.start + "\xff";
    var best;
    factsDb.createReadStream(opts).
        on('data', function(data) {
            console.log(data)
        });

}