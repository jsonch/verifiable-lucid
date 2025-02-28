// A simple count min library. 
// methods: 
// count(key) -- count the key, return updated result
// events / handlers:
// query(key) -- query value of key
// clear(min, max) -- clear indices from min to max


include "verifiableLucid.dfy"


module CountQuery refines VerifiableLucid {

    datatype Event = 
        | query(sport : uint8, key : uint32)
        | response(key : uint32, count : uint32)
        | clear(i : uint32, j : uint32)
    
    // memops
    function incr (oldVal: uint32, incrBy: uint32) : uint32 { 
        to_uint32(oldVal + incrBy) 
    }
    function memval (oldVal: uint32, unused: uint32) : uint32 { oldVal }
    function newval (oldVal: uint32, newVal: uint32) : uint32 { newVal }

    class Program ...{

        const nRows : uint32 := 32
        const seed0 : uint32 := 7
        const seed1 : uint32 := 13

        var col0 : LArray<uint32>
        var col1 : LArray<uint32>
        constructor ()
            ensures fresh(col0)
            ensures fresh(col1)
            ensures col0.cells == zeros(nRows) && col1.cells == zeros(nRows)
            ensures fresh(this)
        {
            col0 := new LArray<uint32>.Create(nRows, 0);
            col1 := new LArray<uint32>.Create(nRows, 0);
        }

        function hash(seed : uint32, key : uint32) : uint32
            ensures 0 <= hash(seed, key) < nRows
        {
            to_uint32((seed + key) % nRows)
        }

        // Increment a key and return current min count
        method count(key : uint32) returns (result : uint32)          
            modifies col0`cells, col1`cells
            requires |col0.cells| == nRows && |col1.cells| == nRows
            requires col0 != col1
            // the result is the minimum of the two counts
            ensures result == 
                var h0 := hash(seed0, key);
                var h1 := hash(seed1, key);
                var count0 := ((  (old(col0.cells)[h0] + 1) % max32));
                var count1 := ((  (old(col1.cells)[h1] + 1) % max32));
                if count0 <= count1 then count0 else count1
            // the arrays are updated correctly
            ensures             
                var h0 := hash(seed0, key);
                var h1 := hash(seed1, key);
                var count0 := to_uint32(old(col0.cells)[h0] + 1 as uint32);
                var count1 := to_uint32(old(col1.cells)[h1] + 1 as uint32);
                LArray.updated_cell(col0, h0, count0)
                && LArray.updated_cell(col1, h1, count1)
        {
            var h0 := hash(seed0, key);
            var h1 := hash(seed1, key);
            var count1 := LArray<uint32>.Update(col0, h0, incr, 1, incr, 1);
            var count2 := LArray<uint32>.Update(col1, h1, incr, 1, incr, 1);
            if (count1 <= count2) {
                result := count1;
            } else {
                result := count2;
            }
        }

        // Query event handler. Generates a response event with the minimum count of the two arrays.
        method Query(sport : uint8, key : uint32)
            modifies this`emittedEvents
            requires readyToHandle(query(sport, key))
            requires |col0.cells| == nRows && |col1.cells| == nRows
            requires col0 != col1
            ensures 
                var h0 := hash(seed0, key);
                var h1 := hash(seed1, key);
                var count0 := old(col0.cells)[h0];
                var count1 := old(col1.cells)[h1];
                var count := if count0 <= count1 then count0 else count1;
                emits(sport, response(key, count))
        {
            var h0 := hash(seed0, key);
            var h1 := hash(seed1, key);
            var count0 := LArray<uint32>.Get(col0, h0, memval, 0);
            var count1 := LArray<uint32>.Get(col1, h1, memval, 0);
            var count := if count0 <= count1 then count0 else count1;
            generate_port(sport, response(key, count));
        }

        // Clear event handler. Clears i, then as long as i < j, clears i+1 by generating a recursive event.
        method Clear(i : uint32, j : uint32)
            modifies col0`cells, col1`cells
            modifies this`generatedEvent
            requires readyToHandle(clear(i, j))
            requires |col0.cells| == nRows && |col1.cells| == nRows
            requires col0 != col1
            requires i < nRows && j < nRows
            ensures 
                LArray.updated_cell(col0, i, 0)
                && LArray.updated_cell(col1, i, 0)
            ensures i < j ==> generates(clear(i + 1, j))
        {
            LArray<uint32>.Set(col0, i, newval, 0);
            LArray<uint32>.Set(col1, i, newval, 0);
            if i < j {
                generate(clear(i + 1, j));
            }
        }            
    }
}