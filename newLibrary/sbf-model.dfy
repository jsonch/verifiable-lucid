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


/*
    What do we want to prove?
    Is it along the lines of:
        lastInsertTime[key] >= (curTs - tInterval) 
            ==> (exists(active, key) || exists(maintain, key))

    How do we even specify this...

*/

/*
TODO: 

we need to straighten out the time / timestamp / rollover logic.

*/

          /*
                assume curTs + delay == tlastRotate
                0 < delay < max32 (so no rollover)
                
                curTs == tlastRotate - delay

                that's impossible. time can't move backwards...




                curTs - tLastRotate 

                This is really complicated, just as complicated as reasoning about timing 
                in the full case study. 

                So we have to find a way to simplify. 

                    Is there an easier way to determine when to switch panes, besides looking at the "time"?
                    And how DO they do it? in verifiable p4?

                    Or will self clocking work?

            */


include "verifiableLucid.dfy"

module SlidingBloomFilter refines VerifiableLucid {
    class Program ... {
        const nRows : uint32 := 32
        const seed0 : uint32 := 7
        const seed1 : uint32 := 13

        var curTs : uint32

        // interval between switching panes
        // we need to see at least nRows packets during this 
        // interval, to clear each entry in the expired pane.
        // lets say its 10 * nRows, which means that 
        // we must see 1 packet every 10 time units.
        const tPktInterArrival : uint32 := 10
        const tinterval : uint32 := tPktInterArrival * nRows

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

        ghost var lastInsertTime : map<uint32, nat> // last key insertion
        ghost var lastOpTime : nat // last operation execution time

        predicate arraySizes ()
        reads this`p0col0, this`p0col1, this`p1col0, this`p1col1, this`p2col0, this`p2col1
        {
               |p0col0| == nRows && |p0col1| == nRows
            && |p1col0| == nRows && |p1col1| == nRows
            && |p2col0| == nRows && |p2col1| == nRows
        }

        twostate predicate arraySizesUnchanged ()
        reads this`p0col0, this`p0col1, this`p1col0, this`p1col1, this`p2col0, this`p2col1
        {
               |p0col0| == |old(p0col0)| && |p0col1| == |old(p0col1)|
            && |p1col0| == |old(p1col0)| && |p1col1| == |old(p1col1)|
            && |p2col0| == |old(p2col0)| && |p2col1| == |old(p2col1)|
        }

        constructor ()
            ensures tLastRotate == 0
            ensures activePane == 0
            ensures clearIdx == 0
            ensures p0col0 == zeros(nRows) && p0col1 == zeros(nRows)
            ensures p1col0 == zeros(nRows) && p1col1 == zeros(nRows)
            ensures p2col0 == zeros(nRows) && p2col1 == zeros(nRows)
            ensures fresh(this)
            ensures lastInsertTime == map[]
            ensures lastOpTime == 0
            ensures curTs == 0
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
            lastInsertTime := map[];
            lastOpTime := 0;
            curTs := 0;
        }

        function hash(seed : uint32, key : uint32) : uint32
            ensures 0 <= hash(seed, key) < nRows
        {
            to_uint32((seed + key) % nRows)
        }

        // memory operations that we want to be atomic in final version

        // update the time since rotate. 
        // if time since tLastRotate is greater than tinterval, return curTs
        // function updateIfTimeElapsed(lastTime : uint32, t : uint32) : uint32
        // {
        //     if (t - lastTime >= tinterval) then (
        //         t
        //      ) else (
        //         lastTime
        //     )
        // }
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

        function nextActive(curActive : uint32) : uint32
            requires 0 <= curActive < 3
        {
            match curActive {
                case 2 => 0
                case _ => curActive + 1
            }
        }

        twostate predicate rotatesOnlyAfterInterval()
            reads this`curTs, this`activePane, this`tLastRotate
        {
            (0 <= old(activePane) < 3) &&
            if   ((curTs - old(tLastRotate)) % max32 >= tinterval)
            then (activePane == nextActive(old(activePane)) && (tLastRotate == curTs % max32))
            else (activePane == old(activePane) && tLastRotate == old(tLastRotate))
        }

        ghost predicate timingInvariant()
            reads this`curTs, this`lastOpTime
        { 
            ((curTs - lastOpTime) % max32) <= tPktInterArrival 
        }

        predicate stateInvariant()
            reads this`activePane, this`clearIdx
        {
            0 <= activePane < 3
            && 0 <= clearIdx < nRows
        }

        predicate clearingPaneAtIndexIsZero()
            reads this`activePane, this`clearIdx
            reads this`p0col0, this`p0col1, this`p1col0, this`p1col1, this`p2col0, this`p2col1
            requires arraySizes ()
            requires 0 <= clearIdx < nRows
            requires 0 <= activePane < 3
        {
            match activePane {
                case 0 => p1col0[clearIdx] == 0 && p1col1[clearIdx] == 0
                case 1 => p2col0[clearIdx] == 0 && p2col1[clearIdx] == 0
                case 2 => p0col0[clearIdx] == 0 && p0col0[clearIdx] == 0
            }
        }

        predicate foundIfSetInActiveOrMaintained(key : uint32)
            reads this`activePane
            reads this`p0col0, this`p0col1, this`p1col0, this`p1col1, this`p2col0, this`p2col1
            requires arraySizes ()
            requires 0 <= activePane < 3
        {
            match activePane {
                case 0 => 
                    keyExistsInPane(key, 0) || keyExistsInPane(key, 2)
                case 1 =>
                    keyExistsInPane(key, 1) || keyExistsInPane(key, 0)
                case 2 =>
                    keyExistsInPane(key, 2) || keyExistsInPane(key, 1)
            }
        }


        /* 
            query reads from the active pane and the maintaining pane,
            and writes to the clearing pane.
            The result is true if both columns in the active pane are true,
            or if both columns in the maintaining pane are true.
        */
        method query(key : uint32)
            returns (res : uint32)
            requires tLastRotate != curTs // I think this is always true.
            requires timingInvariant ()
            requires stateInvariant ()
            requires arraySizes ()
            modifies this`activePane, this`clearIdx, this`tLastRotate
            modifies this`p0col0, this`p0col1, this`p1col0, this`p1col1, this`p2col0, this`p2col1
            modifies this`lastOpTime
            ensures lastOpTime == curTs
            ensures stateInvariant ()
            ensures arraySizesUnchanged ()
            ensures rotatesOnlyAfterInterval () // rotation correctness
            ensures noRemovalsInActiveOrMaintain () // maintenence correctness
            ensures clearingPaneAtIndexIsZero () // clearing correctness -- not complete.. but maybe sufficient?
            ensures foundIfSetInActiveOrMaintained(key) <==> res == 1
        {
            // Question: is it possible for tLastRotate to be 
            // the current timestamp, when the method begins?
            // Answer: No. Because tinterval << max32, and we know we get at least 
            // one message every tinterval.
            // that would require us to not have gotten 
            // any messages since the last rotation interval
            // Bigger question: is there a simpler way to determine when to rotate?
            // and / or is tLastRotate the right thing to track?

            /*
                you could track time since rotate directly?
                packetInterarrival = timestamp - lasttimestamp;
                tSinceRotate = tSinceRotate + packetInterarrival;
                if (tSinceRotate >= tinterval) {
                    tSinceRotate = 0;
                }
            */

            // 1. calculate time since last rotation
            var t_since_last_rotate : uint32 := (curTs - tLastRotate) % max32;
            // rotate and update index, or just update index
            if (t_since_last_rotate >= tinterval) {
                tLastRotate := curTs;
                activePane := updateActivePane(activePane, 0);
                clearIdx := 0;
                assert rotatesOnlyAfterInterval ();
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
            // activePane 0 ==> pane roles = [active, clearing, maintaining]
            // activePane 1 ==> pane roles = [maintaining, active, clearing]
            // activePane 2 ==> pane roles = [clearing, maintaining, active]
            if (activePane == 0) {
                // active = 0, maintaining = 2, clearing = 1
                a0 := p0col0[h0];
                a1 := p0col1[h1];
                p1col0 := p1col0[clearIdx := 0];
                p1col1 := p1col1[clearIdx := 0];
                m0 := p2col0[h0];
                m1 := p2col1[h1];
            } else if (activePane == 1) {
                // active = 1, maintaining = 0, clearing = 2
                m0 := p0col0[h0]; 
                m1 := p0col1[h1];
                a0 := p1col0[h0];
                a1 := p1col1[h1];
                p2col0 := p2col0[clearIdx := 0];
                p2col1 := p2col1[clearIdx := 0];
            } else {
                // active = 2, maintaining = 1, clearing = 0
                p0col0 := p0col0[clearIdx := 0];
                p0col1 := p0col1[clearIdx := 0];
                m0 := p1col0[h0];
                m1 := p1col1[h1];
                a0 := p2col0[h0];
                a1 := p2col1[h1];
            }
            // 3. calculate result: AND columns in same pane, OR across panes
            res := 0;
            if ((a0 == 1 && a1 == 1) || (m0 == 1 && m1 == 1)) {
                res := 1;
            }
            lastOpTime := curTs;
        }

        // A key exists in a pane
        predicate keyExistsIn(c0 : seq<uint32>, c1 : seq<uint32>, key : uint32)
            requires |c0| == nRows && |c1| == nRows            
        {
            c0[hash(seed0, key)] == 1 && c1[hash(seed1, key)] == 1
        }

        predicate keyExistsInActive(key : uint32)
            reads this`p0col0, this`p0col1, this`p1col0, this`p1col1, this`p2col0, this`p2col1
            reads this`activePane
            requires 0 <= activePane < 3
        {
            arraySizes () &&
            match activePane {
                case 0 => keyExistsIn(p0col0, p0col1, key)
                case 1 => keyExistsIn(p1col0, p1col1, key)
                case 2 => keyExistsIn(p2col0, p2col1, key)
            }
        }
        predicate keyExistsInPane(key : uint32, pane : uint32)
            reads this`p0col0, this`p0col1, this`p1col0, this`p1col1, this`p2col0, this`p2col1
            requires 0 <= pane < 3
        {
            arraySizes () &&
            match pane {
                case 0 => keyExistsIn(p0col0, p0col1, key)
                case 1 => keyExistsIn(p1col0, p1col1, key)
                case 2 => keyExistsIn(p2col0, p2col1, key)
            }
        }


        predicate onesPreserved(oldCols : seq<uint32>, cols : seq<uint32>)
        requires |cols| == |oldCols|
        {
            forall i :: 0 <= i < |cols| && oldCols[i] == 1 ==> cols[i] == 1
        }

        twostate predicate noRemovalsInActiveOrMaintain()
            reads this`p0col0, this`p0col1, this`p1col0, this`p1col1, this`p2col0, this`p2col1
            reads this`activePane
            requires 0 <= activePane < 3
        {
            arraySizesUnchanged() &&
            match activePane {
                case 0 => onesPreserved(old(p0col0), p0col0) && onesPreserved(old(p0col1), p0col1) 
                       && onesPreserved(old(p2col0), p2col0) && onesPreserved(old(p2col1), p2col1)
                case 1 => onesPreserved(old(p1col0), p1col0) && onesPreserved(old(p1col1), p1col1) 
                       && onesPreserved(old(p0col0), p0col0) && onesPreserved(old(p0col1), p0col1)
                case 2 => onesPreserved(old(p2col0), p2col0) && onesPreserved(old(p2col1), p2col1) 
                       && onesPreserved(old(p1col0), p1col0) && onesPreserved(old(p1col1), p1col1)
            }
        }

        method insert(key : uint32)
            modifies this`tLastRotate, this`activePane, this`clearIdx
            modifies this`p0col0, this`p0col1, this`p1col0, this`p1col1, this`p2col0, this`p2col1
            modifies this`lastInsertTime, this`lastOpTime
            requires timingInvariant ()
            requires stateInvariant ()
            requires arraySizes ()
            ensures lastOpTime == curTs
            ensures stateInvariant ()
            ensures arraySizesUnchanged ()
            ensures clearingPaneAtIndexIsZero ()
            ensures rotatesOnlyAfterInterval () // rotation correctness
            ensures keyExistsInActive(key) // insertion correctness
            ensures noRemovalsInActiveOrMaintain() // maintenence correctness
            ensures lastInsertTime == old(lastInsertTime)[key := curTs] // ghost insert time update correctness
        {
            // 1. calculate time since last rotation
            var t_since_last_rotate : uint32 := (curTs - tLastRotate) % max32;
            // rotate and update index, or just update index
            if (t_since_last_rotate >= tinterval) {
                tLastRotate := curTs % max32;
                activePane := updateActivePane(activePane, 0);
                clearIdx := 0;
            } else {
                clearIdx := updateClearIdx(clearIdx, 0);
            }

            // 2. write to the active pane at hash indices, 
            //    clear the clearing pane at clearIdx
            // activePane 0 ==> pane roles = [active, clearing, maintaining]
            // activePane 1 ==> pane roles = [maintaining, active, clearing]
            // activePane 2 ==> pane roles = [clearing, maintaining, active]
            var h0 := hash(seed0, key);
            var h1 := hash(seed1, key);
            if (activePane == 0) {
                p0col0 := p0col0[h0 := 1];
                p0col1 := p0col1[h1 := 1];
                p1col0 := p1col0[clearIdx := 0];
                p1col1 := p1col1[clearIdx := 0];
            } else if (activePane == 1) {
                p1col0 := p1col0[h0 := 1];
                p1col1 := p1col1[h1 := 1];
                p2col0 := p2col0[clearIdx := 0];
                p2col1 := p2col1[clearIdx := 0];
            } else {
                p0col0 := p0col0[clearIdx := 0];
                p0col1 := p0col1[clearIdx := 0];
                p2col0 := p2col0[h0 := 1];
                p2col1 := p2col1[h1 := 1];
            }
            lastInsertTime := lastInsertTime[key := curTs];
            lastOpTime := curTs;
        }
    }

    // test a single rotate with a fixed time interval between packets
    method singleRotateTest() {
        var prog := new Program();
        prog.p2col0 := prog.p2col0[0 := 1]; // suppose that something is set somewhere
        assert prog.curTs == 0;
        // insert some key
        prog.insert(1);
        var n := 0;
        while (n < 310) 
            invariant prog.timingInvariant()
            invariant prog.stateInvariant()
            invariant prog.arraySizes ()
            invariant prog.lastOpTime == prog.curTs // the loop starts just after finishing an operation
            invariant prog.curTs == n
            // no rotations in this loop...
            invariant prog.tLastRotate == 0
            invariant prog.activePane == 0            
            invariant prog.keyExistsInActive(1)
        {
            // increment time
            prog.curTs := prog.curTs + 1;
            // do any operation
            label PRE:
            var _ := prog.query(1);
            assert |old@PRE(prog.p0col0)| == |prog.p0col0|;
            assert prog.noRemovalsInActiveOrMaintain@PRE();
            n := n + 1;
        }
        assert prog.curTs == 310;
        assert prog.keyExistsInPane(1, 0);
        // increment time to exactly the rotate time
        prog.curTs := prog.curTs + prog.tPktInterArrival;
        // look for the key, which should both rotate _and_ find it.
        var found := prog.query(1);
        assert prog.activePane == 1;
    }

    type validTime = x : nat | 0 <= x < 10    


    method arbitraryRotateTest() {
        var prog := new Program();
        prog.insert(1); // insert the test key
        assert prog.keyExistsInPane(1, 0);

        var tRemain : nat := prog.tinterval;
        assert prog.curTs == 0;
        assert prog.tLastRotate == 0;
        while (tRemain > 0) 
            invariant prog.curTs + tRemain == prog.tinterval
            invariant prog.curTs <= prog.tinterval
            invariant prog.timingInvariant()
            invariant prog.stateInvariant()
            invariant prog.arraySizes ()
            invariant prog.lastOpTime == prog.curTs // the loop starts just after finishing an operation
            // invariant prog.curTs < prog.tinterval;
        {
            var delay : uint32 := rand(1, prog.tPktInterArrival);
            
            delay := if (delay > tRemain)
                then tRemain
                else delay ;

            assert prog.curTs + delay != prog.tLastRotate;

            prog.curTs := prog.curTs + delay;
            // what if this always held: curTs - lastRotate > 0 
            // 
            assert prog.curTs != prog.tLastRotate;
  

            var _ := prog.query(0); // noop just to maintain clearing
            tRemain := tRemain - delay;
        }
        assert tRemain == 0;

    }

}