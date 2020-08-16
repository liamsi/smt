package smt

import (
	"bytes"
	"crypto/sha256"
	"math/rand"
	"reflect"
	"testing"
)

// Test all tree operations in bulk.
func TestSparseMerkleTree(t *testing.T) {
	for i := 0; i < 5; i++ {
		// Test more inserts/updates than deletions.
		bulkOperations(t, 200, 100, 100, 50)
	}
	for i := 0; i < 5; i++ {
		// Test extreme deletions.
		bulkOperations(t, 200, 100, 100, 500)
	}
}

func BenchmarkInsertsAndUpdates(b *testing.B) {
	tests := []struct {
		name             string
		initialLeavesNum int
		minKeySize       int
		maxKeySize       int
		minValSize       int
		maxValSize       int
		numUpdates       int
	}{
		{"Insert 100 into empty", 0, 16, 32, 1, 64, 100},
		{"Insert 1000 into empty", 0, 16, 32, 1, 64, 1000},
		{"Insert 10000 into empty", 0, 16, 32, 1, 64, 10000},
		{"Insert 50000 into empty", 0, 16, 32, 1, 64, 50000},
		{"Insert 100000 into empty", 0, 16, 32, 1, 64, 100000},
		{"Update 1000 of 1000 leaves (all)", 1000, 16, 32, 1, 64, 1000},
		{"Update 1000 of 100000 leaves", 100000, 16, 32, 1, 64, 1000},
		{"Update 10000 of 100000 leaves", 100000, 16, 32, 1, 64, 10000},
		{"Update 50000 of 100000 leaves", 100000, 16, 32, 1, 64, 50000},
		{"update 100000 of 100000 leaves (all)", 100000, 16, 32, 1, 64, 100000},
	}
	for _, tt := range tests {
		b.Run(tt.name, func(t *testing.B) {
			// setup:
			sm := NewSimpleMap()
			smt := NewSparseMerkleTree(sm, sha256.New())
			initKeys, vals := generateKeyVals(tt.minKeySize, tt.maxKeySize, tt.minValSize, tt.maxValSize, tt.initialLeavesNum)
			for i := 0; i < tt.initialLeavesNum; i++ {
				_, err := smt.Update(initKeys[i], vals[i])
				if err != nil {
					t.Errorf("Update() unxepected error = %v", err)
					return
				}
			}

			keys, vals := generateKeyVals(tt.minKeySize, tt.maxKeySize, tt.minValSize, tt.maxValSize, tt.numUpdates)

			b.ResetTimer()
			// benchmark numUpdates updates:
			for i := 0; i < b.N; i++ {
				for u := 0; u < tt.numUpdates; u++ {
					b.StopTimer()
					var key, val []byte
					// always use new val:
					val = vals[u]
					// re-use a key (update) if possible, else insert
					if u < tt.initialLeavesNum {
						key = initKeys[u]
					} else {
						key = keys[u]
					}
					b.StartTimer()
					_, err := smt.Update(key, val)
					if err != nil {
						t.Errorf("Update() unxepected error = %v", err)
						return
					}
				}
			}
		})
	}
}

func generateKeyVals(
	minKeySize int,
	maxKeySize int,
	minValSize int,
	maxValSize int,
	numLeafs int,
) ([][]byte, [][]byte) {
	keys, vals := make([][]byte, numLeafs), make([][]byte, numLeafs)
	for u := 0; u < numLeafs; u++ {
		keys[u] = randBlob(minKeySize, maxKeySize)
		vals[u] = randBlob(minValSize, maxValSize)
	}
	return keys, vals
}

// generate random bytes with minSize <= num of bytes <= maxSize:
func randBlob(minSize int, maxSize int) []byte {
	keyLen := minSize + rand.Intn(maxSize)
	key := make([]byte, keyLen)
	rand.Read(key)
	return key
}

// Test all tree operations in bulk, with specified ratio probabilities of insert, update and delete.
func bulkOperations(t *testing.T, operations int, insert int, update int, delete int) {
	sm := NewSimpleMap()
	smt := NewSparseMerkleTree(sm, sha256.New())

	max := insert + update + delete
	kv := make(map[string]string)

	for i := 0; i < operations; i++ {
		n := rand.Intn(max)
		if n < insert { // Insert
			keyLen := 16 + rand.Intn(32)
			key := make([]byte, keyLen)
			rand.Read(key)

			valLen := 1 + rand.Intn(64)
			val := make([]byte, valLen)
			rand.Read(val)

			kv[string(key)] = string(val)
			_, err := smt.Update(key, val)
			if err != nil {
				t.Errorf("error: %v", err)
			}
		} else if n > insert && n < insert+update { // Update
			keys := reflect.ValueOf(kv).MapKeys()
			if len(keys) == 0 {
				continue
			}
			key := []byte(keys[rand.Intn(len(keys))].Interface().(string))

			valLen := 1 + rand.Intn(64)
			val := make([]byte, valLen)
			rand.Read(val)

			kv[string(key)] = string(val)
			_, err := smt.Update(key, val)
			if err != nil {
				t.Errorf("error: %v", err)
			}
		} else { // Delete
			keys := reflect.ValueOf(kv).MapKeys()
			if len(keys) == 0 {
				continue
			}
			key := []byte(keys[rand.Intn(len(keys))].Interface().(string))

			kv[string(key)] = ""
			_, err := smt.Update(key, defaultValue)
			if err != nil {
				t.Errorf("error: %v", err)
			}
		}

		bulkCheckAll(t, smt, &kv)
	}
}

func bulkCheckAll(t *testing.T, smt *SparseMerkleTree, kv *map[string]string) {
	for k, v := range *kv {
		value, err := smt.Get([]byte(k))
		if err != nil {
			t.Errorf("error: %v", err)
		}
		if !bytes.Equal([]byte(v), value) {
			t.Error("got incorrect value when bulk testing operations")
		}

		// Generate and verify a Merkle proof for this key.
		proof, err := smt.Prove([]byte(k))
		if err != nil {
			t.Errorf("error: %v", err)
		}
		if !VerifyProof(proof, smt.Root(), []byte(k), []byte(v), smt.th.hasher) {
			t.Error("Merkle proof failed to verify")
		}
		compactProof, err := smt.ProveCompact([]byte(k))
		if err != nil {
			t.Errorf("error: %v", err)
		}
		if !VerifyCompactProof(compactProof, smt.Root(), []byte(k), []byte(v), smt.th.hasher) {
			t.Error("Merkle proof failed to verify")
		}

		if v == "" {
			continue
		}

		// Check that the key is at the correct height in the tree.
		largestCommonPrefix := 0
		for k2, v2 := range *kv {
			if v2 == "" {
				continue
			}
			commonPrefix := countCommonPrefix(smt.th.path([]byte(k)), smt.th.path([]byte(k2)))
			if commonPrefix != smt.depth() && commonPrefix > largestCommonPrefix {
				largestCommonPrefix = commonPrefix
			}
		}
		sideNodes, _, _, err := smt.sideNodesForRoot(smt.th.path([]byte(k)), smt.Root())
		if err != nil {
			t.Errorf("error: %v", err)
		}
		numSideNodes := 0
		for _, v := range sideNodes {
			if v != nil {
				numSideNodes++
			}
		}
		if numSideNodes != largestCommonPrefix+1 && (numSideNodes != 0 && largestCommonPrefix != 0) {
			t.Error("leaf is at unexpected height")
		}
	}
}
