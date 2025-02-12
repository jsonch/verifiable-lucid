/* Experimenting with traits and classes to represent handlers */

module LucidTypes {
    type uint8 = x : nat | 0 <= x < 256
    type uint16 = x : nat | 0 <= x < 65536
    type uint20 = x : nat | 0 <= x < 1048576
    type uint24 = x : nat | 0 <= x < 16777216
    type uint32 = x : nat | 0 <= x < 4294967296
    type uint48 = x : int | 0 <= x < 281474976710656

    const max8 : nat := 256
    const max16 : nat := 65536
    const max20 : nat := 1048576
    const max24 : nat := 16777216
    const max32 : nat := 4294967296
    const max48 : nat := 281474976710656

    function to_uint8(x : int) : uint8
        ensures to_uint8(x) == x % max8
    { x % max8 }

    function to_uint16(x : int) : uint16
        ensures to_uint16(x) == x % max16
    { x % max16 }

    function to_uint20(x : int) : uint20
        ensures to_uint20(x) == x % max20
    { x % max20 }

    function to_uint24(x : int) : uint24
        ensures to_uint24(x) == x % max24
    { x % max24 }

    function to_uint32(x : int) : uint32
        ensures to_uint32(x) == x % max32
    { x % max32 }

}

module Arr {
    import opened LucidTypes
    type  tout<t> = t

    type memcalc<!t> = (t, t) -> tout<t>

    class LArray<t> { // LArray stands for LucidArray
        var cells : seq<t>
        constructor (init_cells : seq<t>) 
        ensures fresh(this)
        ensures cells == init_cells
        {
            cells := init_cells;
        }
        constructor Create(n: nat, init: t)
        ensures fresh(this)
        ensures cells == seq(n, (_ => init))
        {
            cells := seq(n, (_ => init));
        }

        static method  Get<t> (s: LArray<t>, idx: nat, mget: memcalc, garg: t) 
                                                            returns (oldVal: t)
        requires 0 <= idx < |s.cells|
        ensures oldVal == mget(s.cells[idx], garg)
        {
            oldVal := mget (s.cells[idx], garg);
        }

        static method Set<t> (s: LArray<t>, idx:nat, mset: memcalc, sarg: t)      
        modifies s`cells                                   
        requires 0 <= idx < |s.cells|
        ensures |s.cells| == |old(s.cells)|
        // The following line says that newArray is the same as s, except that
        // newArray.cells[idx] is updated to be mset(s.cells[idx], sarg).
        ensures s.cells == old(s.cells)[idx := mset(old(s.cells[idx]), sarg)]
        {
            s.cells := s.cells[idx := mset(s.cells[idx], sarg)];
        }

        static method  Update<t> (s: LArray<t>, idx: nat, mget: memcalc, garg: t,
                                                    mset: memcalc, sarg: t)
                                        returns (oldVal: t)
        modifies s`cells                                   
        requires 0 <= idx < |s.cells|
        ensures oldVal == mget(old(s.cells)[idx], garg)
        ensures |s.cells| == |old(s.cells)|
        // The following line says that newArray is the same as s, except that
        // newArray.cells[idx] is updated to be mset(s.cells[idx], sarg).
        ensures s.cells == old(s.cells)[idx := mset(old(s.cells[idx]), sarg)]
        {
            oldVal := mget (s.cells[idx], garg);
            s.cells := s.cells[idx := mset(s.cells[idx], sarg)];
            // must be called so that s := newVal;
        }

        // onlyChanged is a helper predicate that says that all elements of the array are the same as before, except for the one at index i.
        static twostate predicate updated_cell(s : LArray<t>, i : nat, newVal : t)
            reads s`cells
        {
                0 <= i < |s.cells|
            &&  |s.cells| == |old(s.cells)| 
            &&  s.cells == old(s.cells)[i := newVal]
        }

    }
    // generic memcalc
    function  nocalc<t> (oldVal: t, newArg: t) : t {  oldVal  }
    function  swapcalc<t> (oldVal: t, newArg: t) : t {  newArg  }
}


abstract module VerifiableLucid {
    import opened LucidTypes
    import opened Arr
    type Event(==) 
    predicate unreachable() { false }

    // random nat between s and e, but really just s.
    method rand(s : nat, e : nat) returns (rv : nat)
        requires s < e
        ensures s <= rv < e
    {
        return s;
    }


    class Program {

        const TRecirc : nat := 1 // recirc delay

        var recircQueue : seq<(nat, Event)> // earliest possible arrival time, Event
        var trace : map<nat, Event>
        var handlingRecirc : bool
        var curTime : nat
        constructor ()
            ensures recircQueue == []
            ensures curTime == 0
            ensures trace == map[]
            ensures handlingRecirc == false
        {
            recircQueue := [];
            trace := map[];
            curTime := 0;
            handlingRecirc := false;
        }

        // pick a next recirc event
        method getNextEvent() returns (e : Event)
            modifies this`handlingRecirc
            requires |recircQueue| > 0
            requires recircQueue[0].0 <= curTime
            ensures (e == recircQueue[0].1)
            ensures handlingRecirc
        {
            handlingRecirc := true;
            if (recircQueue[0].0 <= curTime){
                return recircQueue[0].1;
            }
        }

        twostate predicate generated(e : Event) 
            reads this`recircQueue, this`handlingRecirc, this`curTime
        {
                |recircQueue| > 0 
            &&
                (if (handlingRecirc) then (
                     |recircQueue| == |old(recircQueue)|
                ) else (
                    |recircQueue| == |old(recircQueue)| + 1
                ))
            // && 

            // &&  (handlingRecirc ==> |recircQueue| == |old(recircQueue)|)
            // &&  (!handlingRecirc ==> |recircQueue| == |old(recircQueue)| + 1)
            &&  recircQueue[|recircQueue|-1] == (curTime + TRecirc, e)
        }

        // generate a recirc event
        method generate(e : Event) 
            modifies this`recircQueue
            ensures recircQueue == old(recircQueue) + [(curTime + TRecirc, e)]
            {
                recircQueue := recircQueue + [(curTime + TRecirc, e)];
            }

        method clockTick()
            modifies this`curTime, this`handlingRecirc
            ensures curTime == old(curTime) + 1
            ensures handlingRecirc == false
        {
            curTime := curTime + 1;
            handlingRecirc := false;
        }

        // finish processing an event.
        method finish(e : Event) 
            modifies this`recircQueue, this`trace
            requires handlingRecirc ==> |recircQueue| > 0
            ensures (
                if handlingRecirc 
                then (
                    (recircQueue == old(recircQueue)[1..])
                ) else (
                    recircQueue == old(recircQueue)
                )
            )
            // ensures  handlingRecirc ==> (recircQueue == old(recircQueue)[1..])
            // ensures  (!handlingRecirc) ==> recircQueue == old(recircQueue)
            ensures trace == old(trace)[curTime := e]
            {
                if (handlingRecirc) {
                    recircQueue := recircQueue[1..];
                }
                trace := trace[curTime := e];
            }

        // conditions that must be true about the recirculation queue
        // when finished processing an event
        twostate predicate finished(e : Event)
            reads this`handlingRecirc
            reads this`recircQueue
            reads this`trace
            reads this`curTime
        {
            (handlingRecirc ==> |old(recircQueue)| > 0)
            &&
            // recircQueue preserves prefix on handling recirc, except first event
            (handlingRecirc ==> 
                |recircQueue| >= |old(recircQueue)| - 1
                &&
                recircQueue[0..(|old(recircQueue)|-1)] == old(recircQueue)[1..]        
            )        
            &&
            // recircQueue preserves everything on handling non recirc
            ((!handlingRecirc) ==> 

                |recircQueue| >= |old(recircQueue)|
                &&
                recircQueue[0..(|old(recircQueue)|)] == old(recircQueue)      
            )
            &&
            trace == old(trace)[curTime := e]
            && 
            handlingRecirc == old(handlingRecirc)
        }

        predicate canUseCurrentClock()
            reads this`trace, this`curTime
        {
            (curTime !in trace)
        }

        // event arrived from recirc
        predicate recircArrival(e : Event) 
            reads this`recircQueue, this`handlingRecirc, this`trace, this`curTime
            {
                canUseCurrentClock() &&
                handlingRecirc
                && (
                    (|recircQueue| > 0) && (recircQueue[0].1 == e) && (recircQueue[0].0 <= curTime)
                )
            }

        // aevent rrived from non recirc
        predicate networkArrival(e : Event) 
            reads this`recircQueue, this`handlingRecirc, this`trace, this`curTime
            {
                canUseCurrentClock() &&
                !handlingRecirc
            }

        // event arrived from anywhere
        predicate arrival(e : Event) 
            reads this`recircQueue, this`handlingRecirc, this`trace, this`curTime
            {
                canUseCurrentClock() &&
                if (handlingRecirc) then (
                    (|recircQueue| > 0) && (recircQueue[0].1 == e) && (recircQueue[0].0 <= curTime)
                ) else (
                    true
                )
            }
    }
}


module LucidProg refines VerifiableLucid {

// declare some events
datatype Event = 
    | a(x : int)
    | b(y : int)

// declare the "Program", with the handlers and the state
class Program ... {

    method A(x : int) 
        modifies this`recircQueue, this`trace
        requires networkArrival(a(x)) // where does it come from -- the network
        ensures  generated(b(x))      // what does it do: generates an event
        ensures  finished(a(x))       // what does it do: finishes processing an event
    {
        generate(b(x));
        finish(a(x));
    }

    method B(y : int)
        modifies this`recircQueue, this`trace
        requires recircArrival(b(y))
        ensures  finished(b(y))
    {
        finish(b(y));        
    }    
}

// Outside of the program, prove some properties about the trace. 
// For example, you can't process two events on the same cycle.
method traceTest() 
{
    var nextEvent;
    var p := new Program();
    p.A(1); // event a gets handled.
    p.clockTick(); // wait some time
    p.clockTick();
    p.A(1); // another a
    // each A generated an event, so 
    assert |p.recircQueue| == 2;
    p.clockTick();
    nextEvent := p.getNextEvent();
    match nextEvent {case b(x) => p.B(x);}
    p.clockTick();


    nextEvent := p.getNextEvent();
    match nextEvent {case b(x) => p.B(x);}

}

}










