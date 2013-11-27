package main

import (
	"encoding/json"
	"fmt"
	"github.com/syndtr/goleveldb/leveldb"
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
		Deps  []interface{}
		Proof []interface{}
		Dkind int
		Dsig  []interface{}
	}
}

func main() {
	db, err := leveldb.OpenFile("out-v2/facts.leveldb", nil)
	if err != nil {
		fmt.Print(err)
		panic(-1)
	}
	defer db.Close()
	iter := db.NewIterator(nil)
	for iter.Next() {
		// Remember that the contents of the returned slice should not be modified, and
		// only valid until the next call to Next.
		key := iter.Key()
		value := iter.Value()
		fmt.Printf("Key: %s\n", key)
		var fact Fact
		err := json.Unmarshal(value, &fact)
		if err != nil {
			fmt.Printf("Error: %v\nValue: %s\n", err, value)
			panic(-1)
		} else {
			fmt.Printf("Name: %v\n", fact.Skin.Name)
		}
	}
}
