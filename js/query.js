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

var context = {};
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
        }
        cb(null, oldHit.fact);
        return;
    }
    var opts = {start:JSON.stringify(core) + ";"};
    opts.end = opts.start + "\xff";
    var best;
    factsDb.createReadStream(opts).
        on('error', function(err) {
            cb(err, null);
        }).
        on('close', function() {
            /*
            cb("Closed!\n  Query=" + JSON.stringify(opts) +
               "\n  Best=" + JSON.stringify(best), null);
            */
        }).
        on('data', function(data) {
            var fact = new Fact(JSON.parse(data.value));
            //console.log("Queried " + hint.name + " got " + fact.Skin.Name);
            if (!best) {
                best = fact;
            } else if (fact.Skin.Name == hint.name) {
                if ((best.Skin.Name != hint.name) ||
                    ((fact.Tree.Cmd != 'stmt') &&
                     (best.Tree.Cmd == 'stmt'))) {
                    best = fact;
                }
            } else if (fact.Skin.Name == hint.name) {
                console.log("XXXX DUPLICATE! " + hint.name +
                            "\n  fact=" + JSON.stringify(fact) +
                            "\n  best=" + JSON.stringify(best));
            }
        }).
        on('end', function() {
            if (best) {
                if (context.map[best.Skin.Name]) {
                    console.log("# XXXX Already got it");
                    cb(null, best);
                } else {
                    var newNode = {text:null,
                                   prev:null,
                                   next:null};
                    context.map[best.Skin.Name] = {fact: best};
                    var isThm = best.Tree.Cmd !== 'stmt';
                    if (isThm) {
                        context.map[best.Skin.Name].node = newNode;
                    }
                    var where = isThm ? context.proofs : context.iface;
                    newNode.next = where.dll;
                    if (where.dll) {
                        where.dll.prev = newNode;
                    }
                    where.dll = newNode;
                    console.log("# XXXX Getting ghilbert for " +
                                best.Skin.Name +
                                " as " + best.Tree.Cmd);
                    best.toGhilbert(context, function(err, out) {
                        if (err) {
                            console.log("# XXXX Can't get it");
                            cb(err, null);
                        } else {
                            console.log("# XXXX Finished " + best.Skin.Name);
                            newNode.text = out;
                            cb(null, best);
                        }
                    });
                }
            } else {
                cb("Not found!\n  Query=" + JSON.stringify(opts), null);
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

factsDb.get("[[],[0,[0,0,1],[0,[0,1,2],[0,0,2]]],[]];752fd06a4648a2f576d2e65961f7a2b3dfac09a7", function(err, data) {
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