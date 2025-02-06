/* Experimenting with traits and classes to represent handlers */

abstract module Lucid {
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
        // library / base class code
        var curTime : nat
        var recircEvents : map<nat, Event>
        var handledEvents : map<nat, Event>
        const TRecirc : nat := 1 // recirc delay

        predicate init_state()
            reads this`curTime
            reads this`recircEvents
            reads this`handledEvents
        {
            curTime == 0 && recircEvents == map[] && handledEvents == map[]
        }
        constructor () 
        ensures init_state()
        {
            curTime := 0;
            recircEvents := map[];
            handledEvents := map[];
        }        

        method generate(e : Event) 
            modifies this`recircEvents
            requires !(curTime + TRecirc in recircEvents)
            ensures recircEvents == old(recircEvents[(curTime + TRecirc) := e])
        {
            recircEvents := recircEvents[(curTime + TRecirc) := e];
        }

        predicate freeTimeSlot() 
            reads this`curTime, this`handledEvents
        {
            !(curTime in handledEvents)
        }

        predicate noDueRecircs() 
            reads this`curTime, this`recircEvents
        {
            !(exists t :: (t <= curTime) && (t in recircEvents)) // there are no pending recirc events scheduled before or at this time
        }
        predicate noLateRecircs() 
            reads this`curTime, this`recircEvents
        {
            !(exists t :: (t < curTime) && (t in recircEvents)) // there are no pending recirc events scheduled before this time
        }

        predicate nextEvent(e : Event) 
            reads this`curTime, this`recircEvents, this`handledEvents
        {
            noLateRecircs()
            && (curTime in recircEvents ==> recircEvents[curTime] == e) // if there's an event at this time, its e
            && freeTimeSlot()
            && noFutureEventsHandled()
        }

        predicate canGenerate()
            reads this`curTime, this`recircEvents
        {
            !(curTime + TRecirc in recircEvents)
        }

        twostate predicate generated(e : Event) 
            reads this`recircEvents, this`curTime
        {
            recircEvents == (old(recircEvents) - {curTime})[curTime + TRecirc := e]
        }
       twostate predicate nothing_generated()
           reads this`recircEvents
        {            
            recircEvents == old(recircEvents)
        }

        // the event is handled... so set it in handledevents
        predicate handled(e : Event)
            reads this`handledEvents, this`curTime
        {
                curTime in handledEvents 
            &&  handledEvents[curTime] == e
            && noFutureEventsHandled()
        }
        twostate predicate handledRecirc(e : Event)
            reads this`recircEvents, this`curTime, this`handledEvents
        {
            handled(e)
            && recircEvents == old(recircEvents) - {curTime}
        }

        predicate noFutureEventsHandled()
            reads this`handledEvents, this`curTime
        {
            !(exists t :: t in handledEvents && t > curTime)
        }

        // builtin. Do a clock tick, maintaining the given invariant
        method clockTick()
            modifies this`curTime
            requires noFutureEventsHandled()
            requires noDueRecircs()
            ensures curTime == old(curTime + 1)
            ensures noLateRecircs()
            ensures noFutureEventsHandled()
        {
            curTime := curTime + 1;
        }

        method finish(e : Event)
            modifies    this`handledEvents, this`recircEvents
            requires    freeTimeSlot()
            requires     noLateRecircs()
            requires    noFutureEventsHandled()
            ensures     noFutureEventsHandled()
            ensures     noLateRecircs()
            ensures     handledEvents == old(handledEvents)[curTime := e]
            ensures     !(curTime in recircEvents)
            ensures     recircEvents == old(recircEvents) - {curTime}
        {
            recircEvents := recircEvents - {curTime};
            handledEvents := handledEvents[curTime := e];
        }

        // get the next recirculated event
        method getNextEvent() returns (e : Event)
            requires curTime in recircEvents 
            ensures e == recircEvents[curTime]
        {
            return recircEvents[curTime];        
        }


        // to prove properties about infinite sequences, 
        // use this loop invariant to make sure the sequence is well-formed
        predicate loopInvariant() 
            reads this`curTime, this`recircEvents, this`handledEvents
        {
            noLateRecircs()
            && noFutureEventsHandled()
            && forall t :: t in recircEvents ==> t < curTime
        }

    }
}


class Test {

    var foo : nat

    twostate predicate Bar_postcondition()
        reads this`foo
    {
        foo == old(foo) + 1 // problem: old(foo) is not defined.
                            // we could pass it as an argument, but I'd rather not. 
                            // question: is there a cleaner way to do this?
    }

    method Bar() 
        modifies this`foo
        ensures foo == old(foo) + 1
        // Goal: write "ensures Bar_postcondition()" instead of the above
    {
        foo := foo + 1;
    }

}

module ExampleProg refines Lucid {
    // Define events
    datatype Event = 
        | a(x : int)
        | b(y : int)

    // Define handles and state in the "Program" class
    class Program ... {      
        var counter : nat
        constructor () 
        ensures counter == 0
        {
            counter := 0;
        }
        // Translation rule: method A(x) is the handler for event a(x)        
        method A(x : int)
            modifies this`recircEvents, this`handledEvents         
            requires nextEvent(a(x))    // handling the event that just arrived
            requires canGenerate()      // there is room in the recirculation buffer to generate an event that arrives at a specific time
            ensures  handled(a(x))      // we have finished handling the event
            ensures  generated(b(x))    // we have generated a recirculation event
        {
            generate(b(x));   
            finish(a(x));
        }
        method B(x : int)
            modifies this`handledEvents, this`recircEvents, this`counter
            requires nextEvent(b(x))
            ensures handledRecirc(b(x)) 
                // Minor question: can we combine handled and handledRecirc?
                // Something like, if the event is in recircEvents at the current time, 
                // it is removed from recircEvents. 
                // Not sure why it wasn't working last night. Seems simple.
            ensures counter == old(counter) + 1
        {  
            counter := counter + 1;
            finish(b(x));
        }
    }    

    // prove things about finite sequences
    // for example: running A(10) and then B(10) increments the counter
    method A_counts_on_recirc(p : Program) 
        modifies p
        requires p.init_state()
        requires p.counter == 0
        ensures p.counter == 1
    {
        p.A(10);
        p.clockTick();
        assert p.counter == 0; // check something about program state
        var recirculated_event := p.getNextEvent(); // get the recirculated event, fails if there is none.
        match recirculated_event { case b(arg) => p.B(arg); } // destruct and handle the recirculated event.
        assert p.counter == 1; // verify post-condition, not necessary though.

    }

    // prove things about infinite sequences constructed with standard imperative constructs
    // for example: in any infinite sequence of A(1) followed by handling the generated recirc event, followed by a 
    // random wait, the counter will equal the number of times the sequence has completed.
    method A_counts_on_recirc_forever() 
        decreases *
    {
        var p := new Program();
        var nLoops : nat := 0;
        while true
            decreases *
            invariant p.loopInvariant()    // the program's queue state is maintained at every loop start
            invariant p.nextEvent(a(1)) // the next event to be processed is a(1)
            invariant p.counter == nLoops // the interesting program-specific invariant -- the counter counts the number of b events
        {
            p.A(1);
            p.clockTick();
            var recirculated_event := p.getNextEvent();
            match recirculated_event { case b(arg) => p.B(arg); }
            p.clockTick();
            var cur_counter := p.counter;
            var n_ticks_to_wait := rand(1, 10); 
            // wait some more random time, in another loop
            while n_ticks_to_wait > 0
                decreases n_ticks_to_wait
                invariant p.loopInvariant()
                invariant p.nextEvent(a(1))
                invariant p.counter == cur_counter
            {
                p.clockTick();
                n_ticks_to_wait := n_ticks_to_wait - 1;
            }
            // increment loop counteer
            nLoops := nLoops + 1;
        }
    }

    // Next step: 
    // Diagram the architectural model and how the invariants fit in.


}







module LucidTypes {
    type uint8 = x : nat | 0 <= x < 256
    type uint16 = x : nat | 0 <= x < 65536
    type uint20 = x : nat | 0 <= x < 1048576
    type uint24 = x : nat | 0 <= x < 16777216
    type uint32 = x : nat | 0 <= x < 4294967296
    type uint48 = x : int | 0 <= x < 281474976710656
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

    }
    method  Create<t> (n: nat, init: t)
                    returns (newArr : LArray<t>)
        ensures fresh(newArr)
        ensures newArr.cells == seq(n, (_ => init))
    {
        newArr := new LArray(seq(n, (_ => init)));
    }

    method  Get<t> (s: LArray<t>, idx: uint32, mget: memcalc, garg: t) 
                                                        returns (oldVal: t)
    requires 0 <= idx < |s.cells|
    ensures oldVal == mget(s.cells[idx], garg)
    {
        oldVal := mget (s.cells[idx], garg);
    }

    method Set<t> (s: LArray<t>, idx:uint32, mset: memcalc, sarg: t)      
    modifies s`cells                                   
    requires 0 <= idx < |s.cells|
    ensures |s.cells| == |old(s.cells)|
    // The following line says that newArray is the same as s, except that
    // newArray.cells[idx] is updated to be mset(s.cells[idx], sarg).
    ensures s.cells == old(s.cells)[idx := mset(old(s.cells[idx]), sarg)]
    {
        s.cells := s.cells[idx := mset(s.cells[idx], sarg)];
    }

    method  Update<t> (s: LArray<t>, idx: uint32, mget: memcalc, garg: t,
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

    // generic memcalc
    function  nocalc<t> (oldVal: t, newArg: t) : t {  oldVal  }
    function  swapcalc<t> (oldVal: t, newArg: t) : t {  newArg  }
}


