/* Experimenting with traits and classes to represent handlers */

// An event is a datatype / record
datatype Event = 
    | a(x : int)
    | b(y : int)
{
}

// // oh.. a subset of events... hmm... 
// type A = e: Event | e.a? witness *
// type B = e: Event | e.b? witness *


class Program {        
    // trait / base class code
    var curTime : nat
    var recircEvents : map<nat, Event>
    var handledEvents : map<nat, Event>
    const TRecirc : nat := 1 // recirc delay

    method generate(e : Event) 
        modifies this`recircEvents
        requires !(curTime + TRecirc in recircEvents)
        ensures recircEvents == old(recircEvents[(curTime + TRecirc) := e])
    {
        recircEvents := recircEvents[(curTime + TRecirc) := e];
    }

    predicate freeTimeSlot(curTime : nat, handledEvents : map<nat, Event>) {
        !(curTime in handledEvents)
    }

    predicate noDueRecircs(curTime : nat, recircEvents : map<nat, Event>) {
        !(exists t :: (t <= curTime) && (t in recircEvents)) // there are no pending recirc events scheduled before or at this time
    }
    predicate noLateRecircs(curTime : nat, recircEvents : map<nat, Event>) {
        !(exists t :: (t < curTime) && (t in recircEvents)) // there are no pending recirc events scheduled before this time
    }

    predicate validArrival(curTime : nat, recircEvents : map<nat, Event>, handledEvents : map<nat, Event>, e : Event) {
        noLateRecircs(curTime, recircEvents)
        && (curTime in recircEvents ==> recircEvents[curTime] == e) // if there's an event at this time, its e
        && freeTimeSlot(curTime, handledEvents)
        && noFutureEventsHandled(handledEvents, curTime)
    }

    predicate canGenerate(curTime : nat, recircEvents : map<nat, Event>)
    {
        !(curTime + TRecirc in recircEvents)
    }

    predicate didGenerate(oldRecircEvents : map<nat, Event>, recircEvents : map<nat, Event>, curTime : nat, e : Event) 
    {
        recircEvents == oldRecircEvents[curTime + TRecirc := e]
    }
    predicate noGenerate(oldRecircEvents : map<nat, Event>, recircEvents : map<nat, Event>)
    {
        recircEvents == oldRecircEvents
    }

    predicate noFutureEventsHandled(handledEvents : map<nat, Event>, curTime : nat)
    {
        !(exists t :: t in handledEvents && t > curTime)
    }

    // builtin. Do a clock tick without changing anything else.
    method clockTick()
        modifies this`curTime
        requires noFutureEventsHandled(handledEvents, curTime)
        requires noDueRecircs(curTime, recircEvents)
        ensures curTime == old(curTime + 1)
        ensures noLateRecircs(curTime, recircEvents)
        ensures noFutureEventsHandled(handledEvents, curTime)
    {
        curTime := curTime + 1;
    }

    // the event is handled... so set it in handledevents
    predicate handled(handledEvents : map<nat, Event>, curTime : nat, e : Event)
    {
            curTime in handledEvents 
        &&  handledEvents[curTime] == e
        && noFutureEventsHandled(handledEvents, curTime)
    }
    method finish(e : Event)
        modifies    this`handledEvents, this`recircEvents
        requires    freeTimeSlot(curTime, handledEvents)
        requires     noLateRecircs(curTime, recircEvents)
        requires    noFutureEventsHandled(handledEvents, curTime)
        ensures     noFutureEventsHandled(handledEvents, curTime)
        ensures     noLateRecircs(curTime, recircEvents)
        ensures     handledEvents == old(handledEvents)[curTime := e]
        ensures     !(curTime in recircEvents)
        ensures     recircEvents == old(recircEvents) - {curTime}

    {
        recircEvents := recircEvents - {curTime};
        handledEvents := handledEvents[curTime := e];
    }

    // User code
    constructor () 
    ensures curTime == 0
    ensures recircEvents == map[]
    ensures handledEvents == map[]
    {
        curTime := 0;
        recircEvents := map[];
        handledEvents := map[];
    }

    // user handlers
    method A(x : int)
        modifies this`recircEvents, this`handledEvents         
        // requires noFutureEventsHandled(handledEvents, curTime)
        requires validArrival(curTime, recircEvents, handledEvents, a(x)) // the event that this handler represents is valid to arrive next
        // ensures old(recircEvents) == recircEvents
        requires canGenerate(curTime, recircEvents) // There is a free slot in the generate
        ensures  didGenerate(old(recircEvents) - {curTime}, recircEvents, curTime, b(x+1)) // effect  state
        ensures handled(handledEvents, curTime, a(x))
    {
        generate(b(x+1));        
        finish(a(x));
    }

    method B(x : int)
        modifies this`handledEvents, this`recircEvents
        requires validArrival(curTime, recircEvents, handledEvents, b(x)) // the event that this handler represents is valid to arrive next
        requires canGenerate(curTime, recircEvents) // There is a free slot in the generate
        ensures handled(handledEvents, curTime, b(x))
        ensures recircEvents == (old(recircEvents) - {curTime})
        ensures noDueRecircs(curTime, recircEvents)
    {  
        finish(b(x));
        
    }

    // method handle(e: Event) { }

}


// This is decent. 
// The thing remaining is somehow getting the 

method test_recirc() {
    var p := new Program();
    p.A(10);
    p.clockTick();
    p.B(11);
    p.clockTick();
    p.A(10);
}

method test_seq() {
    var p := new Program();
    p.B(11);
    p.clockTick();
    p.clockTick();
    p.B(11);
}











/* What do you need to define along with each event? 

    1. A handler. A state -> state transformation function. 
    2. A pre-condition and post-condition on the state. 
*/









// module Prog refines Lucid {
//     type Event = 
//         | 
// }


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


