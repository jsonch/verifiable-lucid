/*
    A sliding / multi-pane bloom filter. 

    3 panes: 
        active
        maintaining
        clearing

    packet operations: 
        query: 
            - reset next index of clearing
            - take || of all indices in active and maintaining
        insert:
            - reset next index of clearing
            - set all indices in maintaining

    the sequence property of interest: 
        - assuming that packets arrive at a fast enough rate to keep everything clear that should be clear, 
            after you insert a key k, you will be able to query it for at least cycleTime additional time units.
            In psuedocode:
                insert(k) @ t ==> forall t' :: 
                    (t < t' <= t + paneCycleTime)  ==> (query(k) @ t == true)
*/

include "verifiableLucid.dfy"

module SlidingBloomFilter refines VerifiableLucid {
    datatype Event = 
        | insert(key : uint32)
        | query(key: uint32)

    class Program ... {
        const nRows : uint32 := 32
        const seed0 : uint32 := 7
        const seed1 : uint32 := 13

        // interval between switching panes
        // we need to see at least nRows packets during this 
        // interval, to clear each entry in the expired pane.
        // lets say its 10 * nRows, which means that 
        // we must see 1 packet every 10 time units.
        const tinterval : uint32 := 10 * nRows

        var activePane : LArray<uint32> // which pane is active
        var clearIdx   : LArray<uint32> // current index to clear
        // Three panes with 2 columns each
        var p0col0 : LArray<uint32>  // active pane, column 0
        var p0col1 : LArray<uint32>  // active pane, column 1
        var p1col0 : LArray<uint32>  // maintaining pane, column 0
        var p1col1 : LArray<uint32>  // maintaining pane, column 1
        var p2col0 : LArray<uint32>  // clearing pane, column 0
        var p2col1 : LArray<uint32>  // clearing pane, column 1
        
        constructor ()
            ensures fresh(activePane)
            ensures fresh(clearIdx)
            ensures fresh(p0col0) && fresh(p0col1)
            ensures fresh(p1col0) && fresh(p1col1)
            ensures fresh(p2col0) && fresh(p2col1)
            ensures activePane.cells == [0]
            ensures clearIdx.cells == [0]
            ensures p0col0.cells == zeros(nRows) && p0col1.cells == zeros(nRows)
            ensures p1col0.cells == zeros(nRows) && p1col1.cells == zeros(nRows)
            ensures p2col0.cells == zeros(nRows) && p2col1.cells == zeros(nRows)
            ensures fresh(this)
        {
            activePane := new LArray<uint32>.Create(1, 0);
            clearIdx := new LArray<uint32>.Create(1, 0);
            p0col0 := new LArray<uint32>.Create(nRows, 0);
            p0col1 := new LArray<uint32>.Create(nRows, 0);
            p1col0 := new LArray<uint32>.Create(nRows, 0);
            p1col1 := new LArray<uint32>.Create(nRows, 0);
            p2col0 := new LArray<uint32>.Create(nRows, 0);
            p2col1 := new LArray<uint32>.Create(nRows, 0);
        }



        function hash(seed : uint32, key : uint32) : uint32
            ensures 0 <= hash(seed, key) < nRows
        {
            to_uint32((seed + key) % nRows)
        }

        /*
        query:
            ci := clearIndex.update(sat_incr);
            if (activePane == 0) {
                read(p0);
                read(p1);
                write(p2, ci, 0);                

            }

        */



    }    

}