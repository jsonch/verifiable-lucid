/*
This implements a set data structure with a timeout. 
It is meant to model a sliding window bloom filter. 
There are multiple sets, called "panes",
and each pane is active for a certain time interval.
When a pane is active, new elements are inserted into it. 
When the time interval is up, the panes rotate: 
    the active pane becomes a "maintaining" pane. 
    the oldest "maintaining" pane becomes a "clearing" pane.
    and the "clearing" pane becomes the new active pane.
Maintaining panes are read-only, used for querying.
Clearing panes are in the process of being deleted. 
This is the same temporal logic as a sliding window bloom filter, 
just using sets as panes instead of bloom filters.

The SlidingWindowSet class implements the data structure. 
It has two methods that each represent a handler or method: 
    Insert(key) -- inserts the key into the set
    Query(key) -- returns whether the key has been added to the set
- Both methods also rotate the panes and clear the oldest pane as needed.

The most important property of the SlidingWindowSet that has a rotation 
interval of I time units is that if you insert an item into the set at time t,
you will be able to retrieve it until at least time t' < t + I,
regardless of what other operations you perform on the SlidingWindowSet in the meantime.

We prove this property in the "temporalCorrectness" method at the end of the file.
The same approach should also work for a bloom filter implementation.
*/


module SlidingSetTest {
    const T : nat := 64     // total time units -- should be a multiple of K * I
    const K : nat := 4      // number of panes -- this should be fixed at 4
    const I : nat := 8      // number of time units per pane (time between pane rotation)
                            //  -- should be a power of 2 and a factor of T
                            //  -- For the bloom filter implementation, it 
                            //     must also be large enough to allow 
                            //     for a full "clear" operation to take place, 
                            //     which depends on the number of slots in the bloom filter 
                            //     and the minimum assumed rate of incoming events.

    // types for keys, timestamps, and panes, for readability.
    type key = x : nat | 0 <= x < 256 // keys stored in sets.
    type ts = x : nat | 0 <= x < T
    type pane = x : nat | 0 <= x < K

    class SlidingWindowSet {
        var ts : ts
        var pane : pane

        ghost var trueTs : nat
        ghost var trueLastTs : nat

        // The "panes" are sets whose roles rotate each interval
        var p0 : set<key>
        var p1 : set<key>
        var p2 : set<key>
        var p3 : set<key>

        constructor ()
            ensures ts == 0
            ensures trueTs == 0
            ensures trueLastTs == 0
            ensures pane == 0
            ensures p0 == {} && p1 == {} && p2 == {} && p3 == {}
        {
            ts := 0;
            pane := 0;
            trueTs := 0;
            trueLastTs := 0;
            p0, p1, p2, p3 := {}, {}, {}, {};
        }
        function calcPane(ts : ts) : pane 
        {
            ( ts / I ) % K
        }

        ghost predicate timeInvariant ()
            reads this`trueLastTs, this`ts, this`trueTs
        {
                trueTs % T == ts
            &&  trueTs - trueLastTs <= I // Operating assumption -- 
                                         // we get at least 1 packet per rotation interval.

                                         // In the full bloom filter implementation, this would 
                                         // be a smaller interval to make sure that 
                                         // each cell of the bloom filter can be cleared 
                                         // before the rotation.
            
        }


        // describes the effect that a "clear" event / operation has on the state.
        twostate predicate clearEffect ()
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

        // A "clear" event wipes the current "clearing" pane
        method clear()
            modifies this`trueLastTs, this`ts, this`trueTs, this`pane
            modifies this`p0, this`p1, this`p2, this`p3
            requires timeInvariant()
            ensures  timeInvariant()
            ensures  trueLastTs == trueTs
            ensures  pane == calcPane(ts)
            ensures  clearEffect ()
            ensures     unchanged(this`ts)
            ensures     unchanged(this`trueTs)
        {
            pane := calcPane(ts);
            trueLastTs := trueTs;
            match pane {
                case 0 => {p1 := {};}
                case 1 => {p2 := {};}
                case 2 => {p3 := {};}
                case 3 => {p0 := {};}
            }
        }


        method insert(k : key)
            modifies this`trueLastTs, this`ts, this`trueTs, this`pane
            modifies this`p0, this`p1, this`p2, this`p3
            requires timeInvariant()
            ensures  timeInvariant()
            ensures  trueLastTs == trueTs
            ensures  pane == calcPane(ts)
            ensures insertEffect(k)
            ensures  unchanged(this`ts)
            ensures unchanged(this`trueTs)
        {
            // first just calculate pane and update last timestamp.
            pane := calcPane(ts);
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
        }

        method query(k : key) returns (rv : bool)
            // modifies this`lastTs, 
            modifies this`trueLastTs, this`ts, this`trueTs, this`pane
            modifies this`p0, this`p1, this`p2, this`p3
            requires timeInvariant()
            ensures  timeInvariant()
            ensures  trueLastTs == trueTs
            ensures  pane == calcPane(ts)
            ensures  queryEffect(k)
            ensures  rv == queryResult(k)
            ensures  unchanged(this`ts)
            ensures  unchanged(this`trueTs)
        {
            // first calculate pane and update ghost last time.
            pane := calcPane(ts);
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


        // An insert adds a key to the "inserting" pane 
        // and also wipes the current "clearing" pane
        twostate predicate insertEffect (k : key)
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

        twostate predicate queryEffect (k : key)
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

        // The result of a query event
        ghost predicate queryResult (k : key)
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



        // Advance clock simply moves the time forward.
        method advanceClock(delay : nat)
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
    /* Property proof and helpers */

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

    twostate predicate preserved(oldp : set<key>, p : set<key>)
    {
        forall k :: k in oldp ==> k in p
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


    // return a random nat from s to e, inclusive.
    method rand(s : nat, e : nat) returns (rv : nat)
        requires s <= e
        ensures s <= rv <= e
    {
        return s;
    }

    /* 
        The property we want to prove is: 
            if you insert k into a sliding set at time t,             
            then wait until t' such that t' < t + I,
            performing any sequence of query and set operations in the mean time, 
            a query for k at t' will return true.

        We prove this with a method that verifies the property for any possible execution.
    */
    method temporalCorrectness(slidingSet : SlidingWindowSet, k : key, t : nat, t' : nat) returns (found : bool)
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
            invariant slidingSet.trueTs == slidingSet.trueLastTs        // we have just processed a packet
            invariant slidingSet.trueTs == i                            // the time is always set to i
            invariant slidingSet.trueTs - old@L(slidingSet.trueTs) < I  // the time is always within I of start
            
            invariant paneAdvanceLimit@L(slidingSet)    // the pane may only advance by 1 in this time period
                                                        // throughout the loop, the pane that was current at the
                                                        // beginning is always preserved (i.e., not wiped)
            invariant panePreservation@L(slidingSet)    // All elements in the "inserting" pane at label "L"
                                                        // are still in that pane
        {
            var d := rand(1, (t' - i));         // choose a random delay until the next operation
            var rand_key : key := rand(0, 255); // choose a random key
            var rand_op  : nat := rand(0, 1);   // choose randomly between insert and query
            assert slidingSet.timeInvariant();
            assert d < I;
            slidingSet.advanceClock(d);                // update the clock

            assert slidingSet.timeInvariant();
            if (rand_op == 0) {                 // do the chosen operation on the chosen key.
                slidingSet.insert(rand_key);
            } else {
                var _ := slidingSet.query(rand_key);
            }
            // increment the loop counter
            i := i + d;
        }
        // increment clock once more -- this makes trueTs at most I -- and then query the key.
        slidingSet.advanceClock(1);
        found := slidingSet.query(k);
    }
}