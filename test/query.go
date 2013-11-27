package main

import (
	"bytes"
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
		Deps  []string
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
	//start := []byte("[[[0,[1,T0.0],[0,[2,T0.0,[3,T0.1,T0.2]],[4,[2,T0.0,T0.1],[2,T0.0,T0.2]]]],[],[]],")
	start := []byte("[[[0,[1,T0.0],[0,[2,T0.0,[")

	end := append(start, byte(0xff))

	iter.Seek(start)
	for {
		key := iter.Key()
		if bytes.Compare(key, end) > 0 {
			break
		}
		value := iter.Value()
		fmt.Printf("Key: %s\n", key)
		var fact Fact
		err := json.Unmarshal(value, &fact)
		if err != nil {
			fmt.Printf("Error: %v\nValue: %s\n", err, value)
			panic(-1)
		} else {
			fmt.Printf("Name: %v\n", fact.Skin.Name)
			fmt.Printf("Stmt: %v\n", fact.Bone.Stmt)
			//fmt.Printf("End?: %v\n",
			fmt.Println()
		}
		if !iter.Next() {
			break
		}
	}
	iter.Release()
}
