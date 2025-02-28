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

module Helpers {
    datatype Opt<t> = 
    | None()
    | Some(v : t)

    // random nat between s and e, but really just s.
    method rand(s : nat, e : nat) returns (rv : nat)
        requires s < e
        ensures s <= rv < e
    {
        return s;
    }
}

abstract module VerifiableLucid {
    import opened LucidTypes
    import opened Arr
    import opened Helpers


    trait SwitchRuntime {
        const TRecirc : nat := 1 // recirc delay

        var recircQueue : seq<(nat, Event)> // earliest possible arrival time, Event
        var emittedEvents : map<(nat, nat), Event> // (port, time) => event
        var trace : map<nat, Event>
        var handlingRecirc : bool
        var curTime : nat

        var generatedEvent : Opt<Event>

        // generate an event to a port
        method generate_port(p : nat, e : Event)
            modifies this`emittedEvents
            ensures emittedEvents == old(emittedEvents)[(p, curTime) := e]
        {
            emittedEvents := emittedEvents[(p, curTime) := e];
        }
        // condition that an event was emitted to a port at the current time.
        twostate predicate emits(p : nat, e : Event)
            reads this`emittedEvents, this`curTime
        {
               (p, curTime) in emittedEvents 
            && emittedEvents[(p, curTime)] == e
            && emittedEvents == old(emittedEvents)[(p, curTime) := e]
        }

        // recirculation event generation
        twostate predicate generates(e : Event) 
            reads this`generatedEvent
        {
            generatedEvent == Some(e)
        }

        // generate a recirc event
        method generate(e : Event) 
            modifies this`generatedEvent
            requires this.generatedEvent == None()
            ensures  this.generatedEvent == Some(e)
            {
                generatedEvent := Some(e);
            }

        method nextRecirc() returns (e : Event)
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
        // do recirculation queue maintenence, then increment the clock.
        method clockTick()
            modifies this`curTime, this`handlingRecirc, this`generatedEvent, this`recircQueue
            requires handlingRecirc ==> |recircQueue| > 0
            ensures curTime == old(curTime) + 1
            ensures handlingRecirc == false
            ensures generatedEvent == None()
            ensures 
                match (old(handlingRecirc), old(generatedEvent)) {
                    // if we are not handling a recirc, append the generated event (if there is one)
                    case (false, Some(e)) => recircQueue == (old(recircQueue) + [(old(curTime) + TRecirc, e)])
                    case (false, None) => recircQueue == old(recircQueue)
                    // if we _are_ handling a recirc, we also pop that recirc off of the front.
                    case (true, Some(e)) => recircQueue == (old(recircQueue)[1..] + [(old(curTime) + TRecirc, e)])
                    case (true, None) => recircQueue == old(recircQueue)[1..]
                }
        {
            // update recirc queue and state, then tick clock.
            match (handlingRecirc, generatedEvent) {
                case (false, Some(e)) => {
                    recircQueue := recircQueue + [(curTime + TRecirc, e)];
                }
                case (false, None()) => {}
                case (true, Some(e)) => {
                    recircQueue := recircQueue[1..] + [(curTime + TRecirc, e)];
                }
                case (true, None) => {
                    recircQueue := recircQueue[1..];                    
                }
            }
            generatedEvent := None();
            handlingRecirc := false;
            curTime := curTime + 1;
        }

        // Execution trace helpers
        twostate predicate records(e : Event)
            reads this`trace
            reads this`curTime
        {
            trace == old(trace)[curTime := e]            
        }
        method record(e : Event) 
            modifies this`trace
            ensures records(e)
        {
            trace := trace[curTime := e];
        }

        // event is ready to process
        // event arrived from anywhere
        predicate readyToHandle(e : Event) 
            reads this`recircQueue, this`handlingRecirc, this`trace, this`curTime, this`generatedEvent
        {
            generatedEvent == None() &&
            canUseCurrentClock() &&
            (handlingRecirc ==> isNextRecircEvent(e))
        }

        predicate canUseCurrentClock()
            reads this`trace, this`curTime
        {
            (curTime !in trace)
        }

        // event arrived from recirc
        predicate recircArrival(e : Event) 
            reads this`recircQueue, this`handlingRecirc, this`trace, this`curTime, this`generatedEvent
            {
                generatedEvent == None() 
                && canUseCurrentClock() 
                && handlingRecirc
                && isNextRecircEvent(e)
            }

        // event arrived from non recirc
        predicate networkArrival(e : Event) 
            reads this`recircQueue, this`handlingRecirc, this`trace, this`curTime
            {
                canUseCurrentClock() 
                && !handlingRecirc
            }

        predicate isNextRecircEvent(e : Event) 
            reads this`recircQueue, this`handlingRecirc, this`curTime
        {
            (|recircQueue| > 0) && (recircQueue[0].1 == e) && (recircQueue[0].0 <= curTime)
        }
    }

    type Event(==) 
    class Program extends SwitchRuntime {

        // The base constructor just initializes 
        // everything from the switch runtime
        constructor ()
            ensures recircQueue == []
            ensures curTime == 0
            ensures trace == map[]
            ensures handlingRecirc == false
            ensures emittedEvents == map[]
            ensures generatedEvent == None()
        {
            recircQueue := [];
            trace := map[];
            curTime := 0;
            handlingRecirc := false;
            emittedEvents := map[];
            generatedEvent := None();
        }

    }
}

