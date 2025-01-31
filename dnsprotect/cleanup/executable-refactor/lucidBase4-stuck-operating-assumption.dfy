/*-------------------------------------------------------------------------
VERIFIABLE LUCID SIMULATION MODULE FOR REFERENCE IMPLEMENTATIONS WITH
REFINEMENT OF UNBOUNDED NUMBERS AND
REFINEMENT OF EXTERNAL DATA STRUCTURES AND
REFINEMENT OF MEMORY ACCESSES
-------------------------------------------------------------------------*/

/*-------------------------------------------------------------------------
Changes [5-12-2024]

1. add fixed-width int types, replacing "bits" and "counter"
2. updated program to only use fixed-width int types in executable code
3. add a "generate" helper for generating recirculation events, replacing
   event generation by returning from dispatch
4. change "forwarded" to a ghost variable. It is essentially part of 
   the specification.
5. add a "generate_port" helper, for generating output events to a port, 
   use it to implement executable forwarding. Remove "ports" variable.
6. Remove "ensures parameterConstraints ()" in the Constructor, 
   since it cannot ensure parameter constraints of constant parameters
   that are not initialized.
7. Make the filtering decision (line 310) depend on timestamp, not time.
8. Make "time" a ghost parameter, since the implementation does not know 
   the true unbounded time.
9. Put time and timestamp into a "Sys" object, so that the user code 
   does not have to be aware about "TimedEvent"s.
10.Add condition to stateInvariant so that it must hold on 0 args.
11.Move queue and T into Sys.
12.add "Parse" module and parser to verify

----- structural changes -----




-------------------------------------------------------------------------*/


abstract module LucidBase {
   import opened Types
   import opened ParseUtils

   type Event (==)
   datatype TimedEvent = 
      TimedEvent (event: Event, time: nat, timestamp: uint8)
   
   ghost predicate validTimedEvent(te : TimedEvent) {
      te.time % Sys.T == te.timestamp
   }

   datatype RecircCmd = RecircCmd (generate: bool, event: Event)

   datatype GeneratedEvent = Event(event:Event, ports : set<uint8>)

   // system state that can be _read_ by the program, 
   // but may not be _modified_ by the program, or 
   // read by toplevel predicates. 
   class Sys {
      static const T : uint16 := 256          // number must match limit on timestamp
      var time : nat
      ghost var lastTime : nat
      var timestamp : uint8

      constructor ()
      ensures fresh(this)
      ensures freshInit()
       {
         time := 0;
         lastTime := 0;
         timestamp := 0;
      }

      ghost predicate freshInit ()
         reads this
      {
         time == 0 && lastTime == 0 && timestamp == 0
      }
   }

   class Globals {
      constructor ()
         ensures fresh(this)
         ensures parameterConstraints()
         ensures stateInvariant(0, 0, 0)

      ghost predicate parameterConstraints ()          // define in program

      predicate operatingAssumptions (event: Event, time : nat, timestamp: uint8, lastTime:nat)     
         reads this

      ghost predicate stateInvariant (time: nat, timestamp: uint8, lastTime : nat)  
         reads this


      ghost predicate validArrivalTime(
         time:nat,
         timestamp:uint8,
         nextEvent:Event, 
         nextTime:nat,
         nextTimestamp: uint8         
      ) 


      lemma stateInvariantPreservation(
         lastTime:nat,
         time:nat,
         timestamp:uint8,
         nextEvent:Event, 
         nextTime:nat,
         nextTimestamp: uint8
      )
      // If the state invariant currently holds, 
      // and a next event arrives at a valid time
      // and the operating assumptions hold on that next event
      // then the state invariant holds to execute the event
         requires ((time % Sys.T) == timestamp)
         requires ((nextTime % Sys.T) == nextTimestamp)
         requires stateInvariant(time, timestamp, lastTime)
         requires validArrivalTime(time, timestamp, nextEvent, nextTime, nextTimestamp)
         requires operatingAssumptions(nextEvent, nextTime, nextTimestamp, time)
         ensures  stateInvariant(nextTime, nextTimestamp, time)

   }

   class Program {
      var sys : Sys
      var globals : Globals
      var generatedEvents : set<GeneratedEvent>  // the event generated for recirc

      constructor ()                                   // define in program
         ensures fresh(sys)
         ensures fresh(globals)
         ensures fresh(this)
         ensures globals.parameterConstraints()
         ensures globals.stateInvariant(0, 0, 0)

         ensures sys.freshInit()
         ensures generatedEvents == {}
         {
            sys := new Sys();
            globals := new Globals();
            generatedEvents := {};
         }

      method dispatch (e: Event)
         modifies globals                                          // define in program
         modifies this`generatedEvents
         requires sys.timestamp == sys.time % sys.T
         requires globals.parameterConstraints ()
         requires globals.stateInvariant (sys.time, sys.timestamp, sys.lastTime)
         requires globals.operatingAssumptions (e, sys.time, sys.timestamp, sys.lastTime)
         requires generatedEvents == {}
         ensures globals.stateInvariant (sys.time, sys.timestamp, sys.lastTime) 

      method generate(e : Event)            // generate recirculation event
         modifies this`generatedEvents
      {
         generatedEvents := generatedEvents + {Event(e, {})};
      }
      method generate_port(p : uint8, e : Event)  // generate output event
         modifies this`generatedEvents
      {
         generatedEvents := generatedEvents + {Event(e, {p})};
      }

   }

   class Parser {
      static ghost predicate validPacket(p:Packet) 
      static ghost predicate parserSpecification(p : Packet, d : ParseDecision<Event>) 
         requires validPacket(p)
      static function parse(p : Packet) : ParseDecision<Event>
         requires p.offset == 0
         requires validPacket(p) 
         ensures (parserSpecification(p, parse(p)))
   } 

   method runTimedEvent (prog : Program, te : TimedEvent) returns (recircEvents : set<GeneratedEvent>)
      // prog has just finished processing an event, 
      // and now it wants to run this next event at the given time.
      // so:      parameterConstraints hold,
      //          stateInvariant holds at current time
      // ASSUME   the arrival time of the next event is valid
      //          operatingAssumptions hold for the next event at its arrival time
      modifies prog.sys
      modifies prog.globals
      modifies prog`generatedEvents
      requires prog.generatedEvents == {}
      requires prog.sys.time % Sys.T == prog.sys.timestamp
      requires prog.globals.parameterConstraints() // Verified
      requires prog.globals.stateInvariant(prog.sys.time, prog.sys.timestamp, prog.sys.lastTime) // Verified
      requires validTimedEvent(te) // Verified
      requires prog.globals.validArrivalTime(prog.sys.time, prog.sys.timestamp, te.event, te.time, te.timestamp) // Verified
      requires prog.globals.operatingAssumptions(te.event, te.time, te.timestamp, prog.sys.time) // Checked at runtime
      // preserve parameterConstraints and stateInvariant for subsequent event
      ensures  prog.globals.parameterConstraints()
      ensures  prog.globals.stateInvariant(prog.sys.time, prog.sys.timestamp, prog.sys.lastTime)
      ensures  prog.generatedEvents == {}
      ensures  prog.sys.time == te.time
      ensures  prog.sys.timestamp == te.timestamp
      ensures  prog.sys.lastTime == old(prog.sys.time)
   {
      // lemma that the state invariant is preserved.
      prog.globals.stateInvariantPreservation(prog.sys.lastTime, prog.sys.time, prog.sys.timestamp, 
         te.event, te.time, te.timestamp);
      assert prog.globals.stateInvariant(te.time, te.timestamp, prog.sys.time);

      // advance time
      prog.sys.lastTime := prog.sys.time;
      prog.sys.time := te.time;
      prog.sys.timestamp := te.timestamp;

      // dispatch event
      prog.dispatch(te.event);
      // return the generated event...
      recircEvents := prog.generatedEvents;
      prog.generatedEvents := {};
   }

   
   // run a sequence of events, ignoring recirculation events.
   method runTimedEvents(prog : Program, tes : seq<TimedEvent>) 
      modifies prog.sys
      modifies prog.globals
      modifies prog`generatedEvents
      requires |tes| > 0
      // requirements on current state of program
      requires prog.sys.time % Sys.T == prog.sys.timestamp
      requires prog.generatedEvents == {}
      requires prog.globals.stateInvariant(prog.sys.time, prog.sys.timestamp, prog.sys.lastTime)
      requires prog.globals.parameterConstraints()
      // requirement for the first event
      requires prog.globals.validArrivalTime(prog.sys.time, prog.sys.timestamp, tes[0].event, tes[0].time, tes[0].timestamp)
      // requirements for all subsequent events
      requires forall i :: 0 <= i < (|tes|-1) ==> 
         prog.globals.validArrivalTime(tes[i].time, tes[i].timestamp, tes[i+1].event, tes[i+1].time, tes[i+1].timestamp)
      requires forall i :: 0 <= i < |tes| ==> validTimedEvent(tes[i])  
   {
      // check operating assumptions on the current event at runtime
      expect prog.globals.operatingAssumptions(tes[0].event, tes[0].time, tes[0].timestamp, prog.sys.time);

      // // run the current event
      var _ := runTimedEvent(prog, tes[0]);
      // // run subsequent events
      if (|tes| > 1) {
         assert prog.globals.validArrivalTime(tes[0].time, tes[0].timestamp, tes[1].event, tes[1].time, tes[1].timestamp);
         runTimedEvents(prog, tes[1..]);
      }
   }


   ghost predicate singleQueueConstraints(prog : Program,queue1 : seq<TimedEvent>)
   reads prog`sys, prog.sys, prog`globals

   {
      |queue1| > 0 ==> (
         // requirement for the first event
         // 
         prog.globals.validArrivalTime(prog.sys.time, prog.sys.timestamp, queue1[0].event, queue1[0].time, queue1[0].timestamp)
         // requirements for all subsequent events
         && (forall i :: 0 <= i < (|queue1|-1) ==> 
            prog.globals.validArrivalTime(queue1[i].time, queue1[i].timestamp, queue1[i+1].event, queue1[i+1].time, queue1[i+1].timestamp))
         && (forall i :: 0 <= i < |queue1| ==> validTimedEvent(queue1[i])) // trivial: time % T == timestamp
      )
   }


   // run an input trace and the recirculated events that may get generated
   method runInterleaved(prog : Program, queue1 : seq<TimedEvent>, queue2 : seq<TimedEvent>) 
      modifies prog.sys
      modifies prog.globals
      modifies prog`generatedEvents
      requires |queue1| > 0
      // requirements on current state of program
      requires prog.sys.time % Sys.T == prog.sys.timestamp
      requires prog.generatedEvents == {}
      requires prog.globals.stateInvariant(prog.sys.time, prog.sys.timestamp, prog.sys.lastTime)
      requires prog.globals.parameterConstraints()
      requires singleQueueConstraints(prog, queue1)
   {
      // check operating assumptions on the current event at runtime
      expect prog.globals.operatingAssumptions(queue1[0].event, queue1[0].time, queue1[0].timestamp, prog.sys.time);

      // run the current event
      var generatedEvents := runTimedEvent(prog, queue1[0]);


      // // run subsequent events
      if (|queue1| > 1) {
         assert prog.globals.validArrivalTime(queue1[0].time, queue1[0].timestamp, queue1[1].event, queue1[1].time, queue1[1].timestamp);
         runTimedEvents(prog, queue1[1..]);
      }
   }






   class Interpreter {
      // The interpreter is for running a program.
      var prog : Program
      var queue : seq<TimedEvent> // queue of events from outside world.
      constructor (p : Program)
         requires p.sys.freshInit()
         ensures fresh(this)
         ensures prog == p
         ensures prog.sys.freshInit()
         ensures queue == []
         ensures validQueue(queue)
      {
         prog := p;
         queue := [];
      }

      ghost predicate validQueue (q: seq <TimedEvent>)   // queue invariant
      // In a valid queue, times and timestamps match, and time is
      // nondecreasing.
      {
         match |q| {
            case 0 => true
            case _ =>
            (  (  forall j | 0 <= j <= |q|-1 ::
                     q[j].timestamp == q[j].time % Sys.T  )
            && (  forall j | 0 <= j < |q|-1 ::
                     q[j].time <= q[j+1].time  )      )  }
      } 

      // add recirculation events to the queue
      method enqueueRecircEvents (e: Event) returns 
                                                  (recircEvent: TimedEvent)
         requires this.validQueue (this.queue)
         requires |this.queue| > 0              // because method is called just
                    // after dispatch, when dispatched event still in queue
         ensures recircEvent.time > this.queue[|this.queue|-1].time
         ensures recircEvent.timestamp == recircEvent.time % prog.sys.T
      {
         var recircTimestamp: uint8;
         recircTimestamp := (this.queue[|this.queue|-1].timestamp + 1) % prog.sys.T;
         recircEvent := 
                   TimedEvent(e, this.queue[|this.queue|-1].time+1, recircTimestamp);
      }

      method runTimedEvent(te1 : TimedEvent) 
         // advance clock and run timed event. 
         // requires that parameterConstraints, stateInvariant, and operatingAssumptions hold.
         modifies prog.globals
         modifies prog.sys`time, prog.sys`timestamp, prog.sys`lastTime
         modifies prog`generatedEvents
         requires prog.generatedEvents == {} // ignore these for now...
         requires te1.time % prog.sys.T == te1.timestamp // strange that this is not covered anywhere...
         requires prog.globals.parameterConstraints()
         requires prog.globals.stateInvariant(te1.time, te1.timestamp, prog.sys.time)
         requires prog.globals.operatingAssumptions(te1.event, te1.time, te1.timestamp, prog.sys.time)      
         // state invariant is preserved...
         ensures prog.globals.stateInvariant(te1.time, te1.timestamp, prog.sys.lastTime)
         ensures prog.generatedEvents == {} // still empty
      {
         // update time
         prog.sys.lastTime := prog.sys.time;
         prog.sys.time := te1.time;
         prog.sys.timestamp := te1.timestamp;  
         // dispatch the event
         prog.dispatch(te1.event);
         prog.generatedEvents := {};
      }
   }



}


module Memop { 
   type memcalc<!t> = (t, t) -> t

   datatype StateVar<t> = Atomic (val: t)

   method Get<t> (s:StateVar<t>, mget: memcalc, garg: t) returns (oldVal:t)
   ensures oldVal == mget(s.val, garg)
   {
      oldVal := mget (s.val, garg);
   }

   method Set<t> (s: StateVar<t>, mset: memcalc, sarg: t)
                                              returns (newVal: StateVar<t>)
   ensures newVal.val == mset(s.val, sarg)
   {
      newVal := Atomic (mset (s.val, sarg));
      // must be called so that s := newVal;
   }

   method GetSet<t> (s: StateVar<t>, mget: memcalc, garg: t,
                                     mset: memcalc, sarg: t)
                                   returns (oldVal: t, newVal: StateVar<t>)
   ensures oldVal == mget(s.val, garg)
   ensures newVal.val == mset(s.val, sarg)
   {
      oldVal := mget (s.val, garg);
      newVal := Atomic (mset (s.val, sarg));
      // must be called so that s := newVal;
   }

   // generic memcalcs
   function nocalc<t> (oldVal: t, newArg: t) : t {  oldVal  }
   function swapcalc<t> (oldVal: t, newArg: t) : t {  newArg  }
}


module Types {
   // Integer types to use in executable code
   type uint8 = x : nat | 0 <= x < 256
   type uint16 = x : nat | 0 <= x < 65536
   type uint20 = x : nat | 0 <= x < 1048576
   type uint24 = x : nat | 0 <= x < 16777216
   type uint32 = x : nat | 0 <= x < 4294967296
   type uint48 = x : int | 0 <= x < 281474976710656
}

module ParseUtils {
   // Utilities to use in the parser definition
   import opened Types
   // A packet is a sequence of bytes, and a counter that 
   // tracks how many bytes have been read from the packet
   // up to this point.
   datatype Packet = Packet(bytes : seq<uint8>, ghost offset : nat)
   // A parser returns a decision on what to do with the packet
   // either drop it, generate an event defined in the program, 
   // or generate an event defined externally.
   datatype ParseDecision<Event> = 
      | Drop() 
      | Generate(e:Event)
      | GenerateExtern(name:string)

   // Parser helper functions
   // skip n bytes from the packet
   function skip(p : Packet, n : nat) : Packet
      requires (|p.bytes| >= n)
      ensures (skip(p, n).bytes == p.bytes[n..])
   {
      Packet(p.bytes[n..], p.offset + n)
   }

   // read 8 bits (1 byte) from the packet
   function read8(p : Packet) : (Packet, uint8)
      requires (|p.bytes| > 0)
      ensures (read8(p).0.bytes == p.bytes[1..])
   {
      (Packet(p.bytes[1..], p.offset + 1), p.bytes[0])
   }
   function read16(p : Packet) : (Packet, uint16)
      requires (|p.bytes| > 1)
      ensures (read16(p).0.bytes == p.bytes[2..])
   {
      var out : uint16 := 0;
      var out := out + (p.bytes[0] as uint16) * 256;
      var out := out + (p.bytes[1] as uint16);
      (Packet(p.bytes[2..], p.offset + 2), (p.bytes[0] as uint16) * 256 + (p.bytes[1] as uint16))
   }
   function read32(p : Packet) : (Packet, int)
      requires (|p.bytes| > 3)
      ensures (read32(p).0.bytes == p.bytes[4..])
   {
      var out : uint32 := 0;
      var out := out + (p.bytes[0] as uint32) * 256 * 256 * 256;
      var out := out + (p.bytes[1] as uint32) * 256 * 256;
      var out := out + (p.bytes[2] as uint32) * 256;
      var out := out + (p.bytes[3] as uint32);
      (Packet(p.bytes[4..], p.offset + 4), out)
   }
   function read48(p : Packet) : (Packet, int)
      requires (|p.bytes| > 5)
      ensures (read48(p).0.bytes == p.bytes[6..])
   {
      var out : uint48 := 0;
      var out := out + (p.bytes[0] as uint48) * 256 * 256 * 256 * 256 * 256;
      var out := out + (p.bytes[1] as uint48) * 256 * 256 * 256 * 256;
      var out := out + (p.bytes[2] as uint48) * 256 * 256 * 256;
      var out := out + (p.bytes[3] as uint48) * 256 * 256;
      var out := out + (p.bytes[4] as uint48) * 256;
      var out := out + (p.bytes[5] as uint48);
      (Packet(p.bytes[6..], p.offset + 6), out)
   }

   // the classic "network to host short" function
   function ntohs(bs : seq<uint8>) : uint16
      requires (|bs| == 2)
   {
      (bs[0] as uint16) * 256 + (bs[1] as uint16)
   }
   function htons(x : uint16) : seq<uint8>
   {
      [msb(x), lsb(x)]
   }

   function msb(x : uint16) : uint8
   {
      (x / 256) as uint8
   }
   function lsb(x : uint16) : uint8
   {
      (x % 256) as uint8
   }

}
