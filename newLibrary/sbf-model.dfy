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

        var tLastRotate : uint32 // time of last rotation
        var activePane : uint32 // which pane is active
        var clearIdx   : uint32 // current index to clear

        // Three panes with 2 columns each
        var p0col0 : seq<uint32>  // active pane, column 0
        var p0col1 : seq<uint32>  // active pane, column 1
        var p1col0 : seq<uint32>  // maintaining pane, column 0
        var p1col1 : seq<uint32>  // maintaining pane, column 1
        var p2col0 : seq<uint32>  // clearing pane, column 0
        var p2col1 : seq<uint32>  // clearing pane, column 1
        
        constructor ()
            ensures tLastRotate == 0
            ensures activePane == 0
            ensures clearIdx == 0
            ensures p0col0 == zeros(nRows) && p0col1 == zeros(nRows)
            ensures p1col0 == zeros(nRows) && p1col1 == zeros(nRows)
            ensures p2col0 == zeros(nRows) && p2col1 == zeros(nRows)
            ensures fresh(this)
        {
            tLastRotate := 0;
            activePane := 0;
            clearIdx := 0;
            p0col0 := zeros(nRows);
            p0col1 := zeros(nRows);
            p1col0 := zeros(nRows);
            p1col1 := zeros(nRows);
            p2col0 := zeros(nRows);
            p2col1 := zeros(nRows);
        }

        function hash(seed : uint32, key : uint32) : uint32
            ensures 0 <= hash(seed, key) < nRows
        {
            to_uint32((seed + key) % nRows)
        }

        // memory operations that we want to be atomic in final version

        // update the time since rotate. 
        // if time since tLastRotate is greater than tinterval, return curTime
        function updateIfTimeElapsed(lastTime : uint32, curTime : uint32) : uint32
        {
            if (curTime - lastTime >= tinterval) then (
                curTime
             ) else (
                lastTime
            )
        }
        // update the active pane.
        function updateActivePane(storedVal : uint32, unused : uint32) : uint32
            requires 0 <= storedVal < 3
            ensures 0 <= updateActivePane(storedVal, 0) < 3
        {
            if (storedVal == 2) then 0 else (storedVal + 1)
        }
        // update the clear index.
        function updateClearIdx(storedVal : uint32, unused : uint32) : uint32
            requires 0 <= storedVal < nRows
            ensures 0 <= updateClearIdx(storedVal, 0) < nRows
        {
            if (storedVal == nRows - 1) then 0 else (storedVal + 1)
        }

        /* 
            query reads from the active pane and the maintaining pane,
            and writes to the clearing pane.
            The result is true if both columns in the active pane are true,
            or if both columns in the maintaining pane are true.
        */
        method query(key : uint32)
            returns (res : uint32)
            requires 0 <= activePane < 3
            requires 0 <= clearIdx < nRows
            requires |p0col0| == nRows && |p0col1| == nRows
            requires |p1col0| == nRows && |p1col1| == nRows
            requires |p2col0| == nRows && |p2col1| == nRows
            modifies this`activePane, this`clearIdx, this`tLastRotate
            modifies this`p0col0, this`p0col1, this`p1col0, this`p1col1, this`p2col0, this`p2col1
            ensures 0 <= activePane < 3
            ensures 0 <= clearIdx < nRows
        {
            // 1. calculate time since last rotation. 
            //    if it's greater than tinterval, 
            //    rotate panes and update tLastRotate
            tLastRotate := updateIfTimeElapsed(tLastRotate, curTimestamp);
            // we are rotating now
            if (tLastRotate == curTimestamp) {
                activePane := updateActivePane(activePane, 0);
                clearIdx := 0;
            } else {
                clearIdx := updateClearIdx(clearIdx, 0);
            }
            // 2. read from the active and maintaining panes, clear the clearing pane
            var h0 := hash(seed0, key);
            var h1 := hash(seed1, key);
            var a0 := 0;
            var a1 := 0;
            var m0 := 0;
            var m1 := 0;
            if (activePane == 0) {
                // read active and maintaining
                a0 := p0col0[h0];
                a1 := p0col1[h1];
                m0 := p1col0[h0];
                m1 := p1col1[h1];
                // clear stale
                p2col0 := p2col0[clearIdx := 0];
                p2col1 := p2col1[clearIdx := 0];
            } else if (activePane == 1) {
                // read active and maintaining
                a0 := p1col0[h0];
                a1 := p1col1[h1];
                m0 := p2col0[h0];
                m1 := p2col1[h1];
                // clear stale
                p0col0 := p0col0[clearIdx := 0];
                p0col1 := p0col1[clearIdx := 0];
            } else {
                // read active and maintaining
                a0 := p2col0[h0];
                a1 := p2col1[h1];
                m0 := p0col0[h0];
                m1 := p0col1[h1];
                // clear stale
                p1col0 := p1col0[clearIdx := 0];
                p1col1 := p1col1[clearIdx := 0];
            }
            // 3. calculate result: AND columns in same pane, OR across panes
            res := 0;
            if ((a0 == 1 && a1 == 1) || (m0 == 1 && m1 == 1)) {
                res := 1;
            }
        }

        method insert(key : uint32)
            requires 0 <= activePane < 3 
            requires 0 <= clearIdx < nRows
            requires |p0col0| == nRows && |p0col1| == nRows
            requires |p1col0| == nRows && |p1col1| == nRows
            requires |p2col0| == nRows && |p2col1| == nRows
            modifies this`tLastRotate, this`activePane, this`clearIdx
            modifies this`p0col0, this`p0col1, this`p1col0, this`p1col1, this`p2col0, this`p2col1
            ensures 0 <= activePane < 3
            ensures 0 <= clearIdx < nRows
        {
            /* 1. calculate time since last rotation. 
                    - if it's greater than tinterval, 
                      rotate panes and update tLastRotate */
            tLastRotate := updateIfTimeElapsed(tLastRotate, curTimestamp);
            // we are rotating now
            if (tLastRotate == curTimestamp) {
                activePane := updateActivePane(activePane, 0);
                clearIdx := 0;
            } else {
                clearIdx := updateClearIdx(clearIdx, 0);
            }
            // 2. write to the active pane at hash indices, 
            //    clear the clearing pane at clearIdx
            var h0 := hash(seed0, key);
            var h1 := hash(seed1, key);
            if (activePane == 0) {
                p0col0 := p0col0[h0 := 1];
                p0col1 := p0col1[h1 := 1];
                p2col0 := p2col0[clearIdx := 0];
                p2col1 := p2col1[clearIdx := 0];
            } else if (activePane == 1) {
                p0col0 := p0col0[clearIdx := 0];
                p0col1 := p0col1[clearIdx := 0];
                p1col0 := p1col0[h0 := 1];
                p1col1 := p1col1[h1 := 1];
            } else {
                p1col0 := p1col0[clearIdx := 0];
                p1col1 := p1col1[clearIdx := 0];
                p2col0 := p2col0[h0 := 1];
                p2col1 := p2col1[h1 := 1];
            }
        }
    }    

}