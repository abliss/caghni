package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"github.com/syndtr/goleveldb/leveldb"
	"os"
)

type Fact struct {
	Bone struct {
		Stmt interface{}
		Hyps []interface{}
		Free [][]string
	}
	Meat struct {
		Terms []string
		Kinds []string
	}
	Skin struct {
		Name       string
		License    string
		HypNames   []string
		Delimiters []string
		DepNames   []string
		V          [][]string
		T          [][]string
	}
	Tree struct {
		Cmd   string
		Deps  []string
		Proof []interface{}
		Dkind int
		Dsig  []interface{}
	}
}

func get_facts_by_prefix(db *leveldb.DB, start []byte, out chan<- Fact) {
	iter := db.NewIterator(nil)
	end := append(start, byte(0xff))
	iter.Seek(start)
	for {
		key := iter.Key()
		if bytes.Compare(key, end) > 0 {
			break
		}
		value := iter.Value()
		var fact Fact
		err := json.Unmarshal(value, &fact)
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error: %v\nValue: %s\n", err, value)
			panic(-1)
		} else {
			out <- fact
		}
		if !iter.Next() {
			break
		}
	}
	close(out)
	iter.Release()
}

func main() {
	db, err := leveldb.OpenFile("out-v2/facts.leveldb", nil)
	if err != nil {
		fmt.Print(err)
		panic(-1)
	}
	defer db.Close()
	start := []byte("[[[0,[1,T0.0],[0,[2,T0.0,[3,")
	facts := make(chan Fact)
	go get_facts_by_prefix(db, start, facts)
	for {
		fact, ok := <-facts
		if !ok {
			break
		}
		fmt.Printf("Name: %v\n", fact.Skin.Name)
		fmt.Printf("Stmt: %v\n", fact.Bone.Stmt)
		fmt.Println()
	}

}
