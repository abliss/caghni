#!/usr/bin/node
/**
 * query.js
 * Usage: ./query.js dbDir>
 */

var Fact = require('./fact.js');
var Level = require('level');
var Path = require('path');
var Process = process;


// putting [[],[0,[0,0,1],[0,[0,1,2],[0,0,2]]],[]];752fd06a4648a2f576d2e65961f7a2b3dfac09a7 => {"Core":[[],[0,[0,0,1],[0,[0,1,2],[0,0,2]]],[]],"Skin":{"Name":"nic-luk1","HypNames":[],"DepNames":["nic-dfim","nic-bi2","nic-ax","nic-isw2","nic-idel","nic-bi1","nic-idbl","nic-imp","nic-swap","nic-ich","nic-mp"],"VarNames":["ph","ps","ch","ta"],"TermNames":["->","-/\\","<->","/\\","-.","\\/"],"Delimiters":[]},"Tree":{"Cmd":"thm","Deps":[[[[],[0,[0,[0,0,[0,1,1]],[1,0,1]],[0,[0,[0,0,[0,1,1]],[0,0,[0,1,1]]],[0,[1,0,1],[1,0,1]]]],[]],[1,0,2,3,4,5]],[[[[0,[0,1,0],[0,[0,1,1],[0,0,0]]]],[0,0,[0,1,1]],[]],[1,2,0,3,4]],[[[],[0,[0,0,[0,1,2]],[0,[0,3,[0,3,3]],[0,[0,4,1],[0,[0,0,4],[0,0,4]]]]],[]],[1,2,0,3,4]],[[[[0,0,[0,2,1]]],[0,0,[0,1,2]],[]],[1,2,0,3,4]],[[[[0,0,[0,1,2]]],[0,0,[0,1,1]],[]],[1,2,0,3,4]],[[[[0,[0,0,1],[0,[0,0,0],[0,1,1]]]],[0,0,[0,1,1]],[]],[1,2,0,3,4]],[[[[0,1,[0,0,0]]],[0,[0,0,0],[0,[0,1,1],[0,1,1]]],[]],[1,2,0,3,4]],[[[[0,2,[0,1,3]]],[0,[0,0,1],[0,[0,2,0],[0,2,0]]],[]],[1,2,0,3,4]],[[[],[0,[0,0,1],[0,[0,1,0],[0,1,0]]],[]],[1,2,0,3,4]],[[[[0,0,[0,2,2]],[0,2,[0,1,1]]],[0,0,[0,1,1]],[]],[1,2,0,3,4]],[[[1,[0,1,[0,2,0]]],0,[]],[1,2,0,3,4]]],"Proof":[0,1,"Deps.0","Deps.1",0,1,1,3,[1,2,2],"Deps.2","Deps.3","Deps.4",0,2,"Deps.0","Deps.5","Deps.6",[1,[1,2,2],1],"Deps.7",1,2,"Deps.0","Deps.1",1,[1,2,2],"Deps.8","Deps.9",[1,[0,0,2],[0,0,2]],"Deps.7","Deps.9","Deps.9",[0,1,2],[0,0,2],"Deps.0","Deps.5","Deps.9","Deps.9",[0,0,1],[0,[0,1,2],[0,0,2]],"Deps.0","Deps.5","Deps.10"]}}

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
    return n;
}
var context = {};
context.pendingTheorems = {};
context.requestFact = function(core, hint, cb) {
    var oldHit = context.map[hint.name];
    if (oldHit) {
        console.log("Requeried " + hint.name);
        // move to front of dll
        if (oldHit.node) {
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
            if (!context.pendingTheorems[data.key]) {
                var fact = new Fact(JSON.parse(data.value));
                //console.log("Queried " + hint.name + " got " + fact.Skin.Name);
                if (!best || (score(fact, hint) > score(best.fact, hint))) {
                    best = {key: data.key, fact: fact};
                }
            }
        }).
        on('end', function() {
            if (best) {
                if (context.map[best.fact.Skin.Name]) { //XXX key
                    console.log("# XXXX Already got it");
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
                    newNode.next = where.dll;
                    if (where.dll) {
                        where.dll.prev = newNode;
                    }
                    where.dll = newNode;
                    console.log("# XXXX Getting ghilbert for " +
                                best.fact.Skin.Name +
                                " as " + best.fact.Tree.Cmd);

                    best.fact.toGhilbert(context, function(err, out) {
                        if (err) {
                            err += "\n  Ghilbertizing " + best.fact.Skin.Name;
                            cb(err, null);
                        } else {
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

context.iface = {
    dll: null,
}

factsDb.get("[[],[0,[0,0,1],[0,[0,1,2],[0,0,2]]],[]];add30c32799d8ec9a84c54adae34b3dbeb8e128a", function(err, data) {
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


function logDll(node) {
    if (node) {
        console.log("# Text:\n" + node.text);
        logDll(node.next);
    }
}
function finish() {
    console.log("#### IFACE");
    logDll(context.iface.dll);
    console.log("#### PROOFS");
    logDll(context.proofs.dll);
}