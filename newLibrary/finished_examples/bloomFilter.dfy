// A bloom filter with methods for: 
// 1. insert(key)
// 2. query(key)
// 3. clear(idx)
// The filter maintains a ghost "exactSet"
// The properties proven are:
// 1. every key in the exactSet is in the filter
// 2. insert(key) adds key to the exactSet and filter, preserving (1.)
// 3. query(key) only returns 1 if it is in the filter

include "verifiableLucid.dfy"

module BloomFilter refines VerifiableLucid {

    // No events -- this is a library

    // memops
    function memval (oldVal: uint32, unused: uint32) : uint32 { oldVal }
    function newval (oldVal: uint32, newVal: uint32) : uint32 { newVal }

    class Program ... {

        const nRows : uint32 := 1024
        const seed0 : uint32 := 7
        const seed1 : uint32 := 13
        var col0 : LArray<uint32>
        var col1 : LArray<uint32>

        ghost var exactSet : set<uint32>

        ghost var ArrayRepr : set<object>
        ghost predicate ValidArrays()
            reads this, ArrayRepr
        {
            col0 in ArrayRepr && col1 in ArrayRepr
            && |col0.cells| == nRows && |col1.cells| == nRows
            && |{col0, col1}| == 2
        }

        constructor ()
            ensures fresh(col0)
            ensures fresh(col1)
            ensures col0.cells == zeros(nRows) && col1.cells == zeros(nRows)
            ensures ValidArrays()
            ensures fresh(this)
        {
            col0 := new LArray<uint32>.Create(nRows, 0);
            col1 := new LArray<uint32>.Create(nRows, 0);
            ArrayRepr := {col0, col1};
        }
        function hash(seed : uint32, key : uint32) : uint32
            ensures 0 <= hash(seed, key) < nRows
        {
            to_uint32((seed + key) % nRows)
        }

        ghost predicate inFilter(key : uint32)
            reads this, ArrayRepr
            requires ValidArrays()
        {
            var h0 := hash(seed0, key);
            var h1 := hash(seed1, key);
            var count0 := to_uint32((col0.cells)[h0] as uint32);
            var count1 := to_uint32((col1.cells)[h1] as uint32);            
            count0 == 1 && count1 == 1
        }

        method insert(key : uint32)
            modifies ArrayRepr, this`exactSet
            requires ValidArrays()
            requires forall k :: k in exactSet ==> inFilter(k)
            ensures ValidArrays()
            ensures exactSet == old(exactSet) + {key}
            ensures forall k :: k in  exactSet ==> inFilter(k)
        {
            var h0 := hash(seed0, key);
            var h1 := hash(seed1, key);
            exactSet := exactSet + {key};
            LArray<uint32>.Set(col0, h0, newval, 1);
            LArray<uint32>.Set(col1, h1, newval, 1);
        }

        method query(key : uint32) returns (found : uint32)
            requires ValidArrays()
            requires forall k :: k in exactSet ==> inFilter(k)
            ensures found == 1 <==> inFilter(key)
        {
            var h0 := hash(seed0, key);
            var h1 := hash(seed1, key);
            var c0 := LArray<uint32>.Get(col0, h0, memval, 0);
            var c1 := LArray<uint32>.Get(col1, h1, memval, 0);
            if (c0 == 1 && c1 == 1) {
                found := 1;
            } else {
                found := 0;
            }
        }

        method clear(idx : uint32)
            modifies ArrayRepr
            requires idx < nRows
            requires ValidArrays()
            ensures  ValidArrays()
        {
            LArray<uint32>.Set(col0, idx, newval, 0);
            LArray<uint32>.Set(col1, idx, newval, 0);
        }
    }
}