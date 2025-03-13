// random nat between s and e, but really just s.
method rand(s : nat, e : nat) returns (rv : nat)
    requires s < e
    ensures s <= rv < e
{
    return s;
}


module SlidingSetTest {
    type key = x : nat | 0 <= x < 256
    type ts = x : nat | 0 <= x < T
    type pane = x : nat | 0 <= x < 4
    const T : nat := 32 // total time units
    // const I : nat := 64 // time between packets
    const K : ts := 4 // number of panes
        // so with K == 4 and T == 32, we have 8 time units per pane
    // const I : nat := T / K // max time between packets
    const I : nat := 4 // time between pane rotation
    // T should be a multiple of K * I

    class SlidingWindowSet {
        var ts : ts
        var lastTs : ts
        var pane : pane

        ghost var trueTs : nat
        ghost var trueLastTs : nat

        // the panes.
        var p0 : set<key>
        var p1 : set<key>
        var p2 : set<key>
        var p3 : set<key>

        constructor ()
            ensures ts == 0
            ensures lastTs == 0
            ensures trueTs == 0
            ensures trueLastTs == 0
            ensures pane == 0
            ensures p0 == {}
            ensures p1 == {}
            ensures p2 == {}
            ensures p3 == {}
        {
            lastTs := 0;
            ts := 0;
            pane := 0;
            trueTs := 0;
            trueLastTs := 0;
            p0 := {};
            p1 := {};
            p2 := {};
            p3 := {};
        }
        function calcPane(ts : ts) : pane 
        {
            (ts / I ) % K
        }

        function calcTruePane(realTs : nat) : nat 
        {
            ((realTs % T) / I )% K
        }

        lemma paneEqTruePane(ts : ts, time : nat)
            requires ts == time % T
            ensures calcPane(ts) == calcTruePane(time)
        { }

        ghost predicate timeInvariant ()
            reads this`lastTs, this`trueLastTs, this`ts, this`trueTs
        {
                trueTs % T == ts
            &&  trueLastTs % T == lastTs
            // &&  ts - lastTs <= I // must get at least 1 packet per interval, to do the rotate
        }

        // rotate is basically a noop -- nothing changes, just the pane.        
        method rotate()
            modifies this`lastTs, this`trueLastTs, this`ts, this`trueTs, this`pane
            requires timeInvariant()
            requires calcPane(lastTs) == calcTruePane(trueLastTs)
            ensures  timeInvariant()
            ensures  calcPane(ts) == calcTruePane(trueTs)
            ensures  trueLastTs == trueTs
            ensures  pane == calcPane(ts)
            ensures  unchanged(this`ts)
            ensures  unchanged(this`trueTs)
        {
            pane := calcPane(ts);
            lastTs := ts;
            trueLastTs := trueTs;
        }

        twostate predicate clearUpdate ()
        reads this`pane
        reads this`p0, this`p1, this`p2, this`p3
        {
            match pane {
                case 0 => p0 == old(p0) && p1 == {} && p2 == old(p2) && p3 == old(p3)
                case 1 => p0 == old(p0) && p1 == old(p1) && p2 == {} && p3 == old(p3)
                case 2 => p0 == old(p0) && p1 == old(p1) && p2 == old(p2) && p3 == {}
                case 3 => p0 == {} && p1 == old(p1) && p2 == old(p2) && p3 == old(p3)
            }
        }        

        // only do the clear part
        method clear()
            modifies this`lastTs, this`trueLastTs, this`ts, this`trueTs, this`pane
            modifies this`p0, this`p1, this`p2, this`p3
            requires timeInvariant()
            requires calcPane(lastTs) == calcTruePane(trueLastTs)
            ensures  timeInvariant()
            ensures  calcPane(ts) == calcTruePane(trueTs)
            ensures  trueLastTs == trueTs
            ensures  pane == calcPane(ts)
            ensures clearUpdate()
            ensures     unchanged(this`ts)
            ensures     unchanged(this`trueTs)
        {
            pane := calcPane(ts);
            lastTs := ts;
            trueLastTs := trueTs;
            match pane {
                case 0 => {p1 := {};}
                case 1 => {p2 := {};}
                case 2 => {p3 := {};}
                case 3 => {p0 := {};}
            }
        }        

        twostate predicate insertUpdate (k : key)
        reads this`pane
        reads this`p0, this`p1, this`p2, this`p3
        {
            match pane {
                case 0 => p0 == old(p0) + {k} && p1 == {} && p2 == old(p2) && p3 == old(p3)
                case 1 => p0 == old(p0) && p1 == old(p1) + {k} && p2 == {} && p3 == old(p3)
                case 2 => p0 == old(p0) && p1 == old(p1) && p2 == old(p2) + {k} && p3 == {}
                case 3 => p0 == {} && p1 == old(p1) && p2 == old(p2) && p3 == old(p3) + {k}
            }
        }

        method insert(k : key)
            modifies this`lastTs, this`trueLastTs, this`ts, this`trueTs, this`pane
            modifies this`p0, this`p1, this`p2, this`p3
            requires timeInvariant()
            requires calcPane(lastTs) == calcTruePane(trueLastTs)
            ensures  timeInvariant()
            ensures  calcPane(ts) == calcTruePane(trueTs)
            ensures  trueLastTs == trueTs
            ensures  pane == calcPane(ts)
            ensures insertUpdate(k)
            ensures  unchanged(this`ts)
            ensures unchanged(this`trueTs)
        {
            // first just calculate pane and update timestamp.
            pane := calcPane(ts);
            lastTs := ts;
            trueLastTs := trueTs;
            // next, insert into the appropriate pane.
            match pane {
                case 0 => {p0 := p0 + {k};}
                case 1 => {p1 := p1 + {k};}
                case 2 => {p2 := p2 + {k};}
                case 3 => {p3 := p3 + {k};}
            }
            // finally, make sure the clearing pane is empty.
            // (we are clearing the pane that will be the next active one)
            match pane {
                case 0 => {p1 := {};}
                case 1 => {p2 := {};}
                case 2 => {p3 := {};}
                case 3 => {p0 := {};}
            }
            assert (insertUpdate(k) && pane == 0) ==> k in p0;
        }

        twostate predicate queryUpdate (k : key)
        reads this`pane
        reads this`p0, this`p1, this`p2, this`p3
        {
            // this predicate should just express that 
            // the appropriate pane is cleared and the others are unchanged.
            match pane {
                case 0 => p0 == old(p0) && p1 == {} && p2 == old(p2) && p3 == old(p3)
                case 1 => p0 == old(p0) && p1 == old(p1) && p2 == {} && p3 == old(p3)
                case 2 => p0 == old(p0) && p1 == old(p1) && p2 == old(p2) && p3 == {}
                case 3 => p0 == {} && p1 == old(p1) && p2 == old(p2) && p3 == old(p3)
            }
        }

        predicate queryResult (k : key)
        reads this`pane
        reads this`p0, this`p1, this`p2, this`p3
        {
            // query returns true if the key is in the current pane or the previous pane.
            match pane {
                case 0 => (k in p0 || k in p3)
                case 1 => (k in p1 || k in p0)
                case 2 => (k in p2 || k in p1)
                case 3 => (k in p3 || k in p2)
            }
        }

        method query(k : key) returns (rv : bool)
            modifies this`lastTs, this`trueLastTs, this`ts, this`trueTs, this`pane
            modifies this`p0, this`p1, this`p2, this`p3
            requires timeInvariant()
            requires calcPane(lastTs) == calcTruePane(trueLastTs)
            ensures  timeInvariant()
            ensures  calcPane(ts) == calcTruePane(trueTs)
            ensures  trueLastTs == trueTs
            ensures  pane == calcPane(ts)
            ensures  queryUpdate(k)
            ensures  rv == queryResult(k)
            ensures  unchanged(this`ts)
            ensures  unchanged(this`trueTs)
        {
            // first just calculate pane and update timestamp.
            pane := calcPane(ts);
            lastTs := ts;
            trueLastTs := trueTs;
            // next, query the pane and the previous pane for the key.
            match pane {
                case 0 => {rv := k in p0 || k in p3;}
                case 1 => {rv := k in p1 || k in p0;}
                case 2 => {rv := k in p2 || k in p1;}
                case 3 => {rv := k in p3 || k in p2;}
            }
            // finally, make sure the clearing pane is empty.
            match pane {
                case 0 => {p1 := {};}
                case 1 => {p2 := {};}
                case 2 => {p3 := {};}
                case 3 => {p0 := {};}
            }            
        }

        // Update the clock
        method clock(delay : nat)
            modifies this`ts, this`trueTs
            requires ts == trueTs % T
            ensures ts == trueTs % T
            ensures trueTs == old(trueTs) + delay
            ensures ts == (old(ts) + delay) % T
        {
            trueTs := trueTs + delay;
            ts := (ts + delay) % T;
        }

    }

    // method test()
    // {
    //     var rv : bool;
    //     var slidingSet := new SlidingWindowSet();
    //     assert slidingSet.timeInvariant();
    //     assert slidingSet.pane == 0;
    //     assert slidingSet.ts == 0;
    //     assert slidingSet.p0 == {};
    //     assert slidingSet.p1 == {};
    //     slidingSet.insert(1);
    //     assert 1 in slidingSet.p0;
    //     rv := slidingSet.query(1);
    //     assert rv;
    //     slidingSet.clock(1);
    //     rv := slidingSet.query(1);
    //     assert rv;
    // }

    twostate predicate preserved(oldp : set<key>, p : set<key>)
    {
        forall k :: k in oldp ==> k in p
    }

    
    // method clearTest_almost(slidingSet : SlidingWindowSet, testKey : key, t' : nat)
    //     modifies slidingSet
    //     requires slidingSet.timeInvariant()
    //     requires t' < I // Not quite what we want. 
    // {
    //     // Insert the test key into the timer.
    //     slidingSet.insert(testKey);
    //     label L: // remember the state at this point.
    //     var i := 0;
    //     while (i < t')
    //         invariant i <= (I - 1)
    //         invariant slidingSet.timeInvariant()
    //         invariant slidingSet.trueTs == old@L(slidingSet.trueTs) + i
    //         invariant slidingSet.ts == (old@L(slidingSet.ts) + i) % T
    //         // the pane may only advance by 1 in this time period.
    //         invariant (
    //             match (old@L(slidingSet.pane)) {
    //                 case 0 => slidingSet.pane == 0 || slidingSet.pane == 1
    //                 case 1 => slidingSet.pane == 1 || slidingSet.pane == 2
    //                 case 2 => slidingSet.pane == 2 || slidingSet.pane == 3
    //                 case 3 => slidingSet.pane == 3 || slidingSet.pane == 0
    //             }
    //         )
    //         // throughout the loop, the pane that was current at the
    //         // beginning is always preserved (i.e., not wiped)
    //         invariant
    //             match old@L(slidingSet.pane) {
    //                 case 0 => 
    //                     preserved(old@L(slidingSet.p0), slidingSet.p0)
    //                     && preserved(old@L(slidingSet.p3), slidingSet.p3)
    //                 case 1 =>
    //                     preserved(old@L(slidingSet.p1), slidingSet.p1)
    //                     && preserved(old@L(slidingSet.p0), slidingSet.p0)
    //                 case 2 =>
    //                     preserved(old@L(slidingSet.p2), slidingSet.p2)
    //                     && preserved(old@L(slidingSet.p1), slidingSet.p1)
    //                 case 3 =>
    //                     preserved(old@L(slidingSet.p3), slidingSet.p3)
    //                     && preserved(old@L(slidingSet.p2), slidingSet.p2)
    //             }
    //     {
    //         slidingSet.clock(1);
    //         slidingSet.clear();
    //         i := i + 1;
    //     }
    //     var rv : bool;
    //     rv := slidingSet.query(testKey);
    //     assert rv;

    // }


    twostate predicate paneAdvanceLimit(slidingSet : SlidingWindowSet)
        reads slidingSet`pane
    {
        match (old(slidingSet.pane)) {
            case 0 => slidingSet.pane == 0 || slidingSet.pane == 1
            case 1 => slidingSet.pane == 1 || slidingSet.pane == 2
            case 2 => slidingSet.pane == 2 || slidingSet.pane == 3
            case 3 => slidingSet.pane == 3 || slidingSet.pane == 0
        }
    }
    twostate predicate panePreservation(slidingSet : SlidingWindowSet)
        reads slidingSet`pane, slidingSet`p0, slidingSet`p1, slidingSet`p2, slidingSet`p3
    {
        match old(slidingSet.pane) {
            case 0 => 
                preserved(old(slidingSet.p0), slidingSet.p0)
                && preserved(old(slidingSet.p3), slidingSet.p3)
            case 1 =>
                preserved(old(slidingSet.p1), slidingSet.p1)
                && preserved(old(slidingSet.p0), slidingSet.p0)
            case 2 =>
                preserved(old(slidingSet.p2), slidingSet.p2)
                && preserved(old(slidingSet.p1), slidingSet.p1)
            case 3 =>
                preserved(old(slidingSet.p3), slidingSet.p3)
                && preserved(old(slidingSet.p2), slidingSet.p2)
        }
    }
    /*
        Inserting key k into the sliding set at time t, 
        then performing 1 clear operation per time-unit until t', 
        and finally querying the set for k at time t' such that t' < t + I, 
        will return the key. */
    // method clearTest(slidingSet : SlidingWindowSet, k : key, t : nat, t' : nat)
    //     modifies slidingSet
    //     requires slidingSet.timeInvariant()
    //     requires slidingSet.trueTs == t
    //     requires t <= t' < t + I
    // {
    //     // Insert the test key into the sliding set.
    //     slidingSet.insert(k);
    //     label L: // remember the state at this point.
    //     var i := t; // set up the timing loop.
    //     while (i < t')
    //         invariant i < t + I
    //         invariant slidingSet.timeInvariant()
    //         invariant slidingSet.trueTs == i
    //         invariant slidingSet.trueTs == old@L(slidingSet.trueTs) - t + i
    //         // the pane may only advance by 1 in this time period.
    //         invariant paneAdvanceLimit@L(slidingSet)
    //         // throughout the loop, the pane that was current at the
    //         // beginning is always preserved (i.e., not wiped)
    //         invariant panePreservation@L(slidingSet)
    //     {
    //         slidingSet.clock(1);
    //         slidingSet.clear();
    //         i := i + 1;
    //     }
    //     var rv : bool;
    //     rv := slidingSet.query(k);
    //     assert rv;
    // }

    method rand(s : nat, e : nat) returns (rv : nat)
        requires s <= e
        ensures s <= rv <= e
    {
        return s;
    }

    // Now, vary the interarrival time of operations, within bounds.
    // method clearTestTime(slidingSet : SlidingWindowSet, k : key, t : nat, t' : nat)
    //     modifies slidingSet
    //     requires slidingSet.timeInvariant()
    //     requires slidingSet.trueTs == t
    //     requires t < t' < t + I
    // {
    //     // Insert the test key into the sliding set.
    //     slidingSet.insert(k);
    //     label L: // remember the state at this point.
    //     var i := t; // the loop starts at time t.
    //     while (i < t') // and continues until t'
    //         invariant i <= t'
    //         invariant slidingSet.timeInvariant()
    //         invariant slidingSet.trueTs == i // the time is always set to i
    //         invariant slidingSet.trueTs - old@L(slidingSet.trueTs) < I // the time is always within I of start.
    //         // the pane may only advance by 1 in this time period.
    //         invariant paneAdvanceLimit@L(slidingSet)
    //         // throughout the loop, the pane that was current at the
    //         // beginning is always preserved (i.e., not wiped)
    //         invariant panePreservation@L(slidingSet)
    //     {
    //         var d := rand(1, (t' - i)); // choose the delay until the next operation.
    //         slidingSet.clock(d);
    //         slidingSet.clear();
    //         i := i + d;
    //     }
    //     // increment to t' + 1 (which can be up to I) and retrieve the key.
    //     slidingSet.clock(1);
    //     var rv : bool;
    //     rv := slidingSet.query(k);
    //     assert rv;
    // }

    // Finally, vary the operation type.
    method fullProperty(slidingSet : SlidingWindowSet, k : key, t : nat, t' : nat) returns (found : bool)
        modifies slidingSet
        requires slidingSet.timeInvariant()
        requires slidingSet.trueTs == t
        requires t < t' < t + I
        ensures  found
    {
        // Insert the test key into the sliding set.
        slidingSet.insert(k);
        label L: // remember the state at this point.
        var i := t; // the loop starts at time t.
        while (i < t') // and continues until t'
            invariant i <= t'
            invariant slidingSet.timeInvariant()
            invariant slidingSet.trueTs == i // the time is always set to i
            invariant slidingSet.trueTs - old@L(slidingSet.trueTs) < I // the time is always within I of start.
            // the pane may only advance by 1 in this time period.
            invariant paneAdvanceLimit@L(slidingSet)
            // throughout the loop, the pane that was current at the
            // beginning is always preserved (i.e., not wiped)
            invariant panePreservation@L(slidingSet)
        {
            var d := rand(1, (t' - i));         // choose the delay until the next operation.
            slidingSet.clock(d);                // update the clock
            var rand_key : key := rand(0, 255); // choose a random key
            var rand_op  : nat := rand(0, 1);   // choose randomly between insert and query
            // do the chosen operation.
            if (rand_op == 0) {
                slidingSet.insert(rand_key);
            } else {
                var _ := slidingSet.query(rand_key);
            }
            // increment the loop counter
            i := i + d;
        }
        // increment clock once more -- this makes it at most I -- and then query the key.
        slidingSet.clock(1);
        found := slidingSet.query(k);
    }

}