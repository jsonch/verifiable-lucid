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
-------------------------------------------------------------------------*/


abstract module LucidBase {
   import opened Types

   type Event (==)
   datatype TimedEvent = 
      TimedEvent (event: Event, ghost time: nat, timestamp: uint8)
            
   datatype RecircCmd = RecircCmd (generate: bool, event: Event)

   datatype GeneratedEvent = Event(event:Event, ports : set<uint8>)

   // system state that can be _read_ by the program, 
   // but may not be _modified_ by the program, or 
   // read by toplevel predicates. 
   class Sys {
      static const T : uint16 := 256          // number must match limit on timestamp
      ghost var time : nat
      ghost var lastTime : nat
      var timestamp : uint8
      var queue : seq <TimedEvent>

      constructor ()
      ensures fresh(this)
      ensures validQueue(queue)
       {
         time := 0;
         lastTime := 0;
         timestamp := 0;
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
                     q[j].timestamp == q[j].time % T  )
            && (  forall j | 0 <= j < |q|-1 ::
                     q[j].time <= q[j+1].time  )      )  }
      } 
   }

   class Interpreter {
      // The interpreter is for running a program.
      var prog : Program
      var sys : Sys
      constructor (p : Program)
         ensures fresh(this)
         ensures sys == prog.sys
         {
            prog := p;
            sys := p.sys;
         }

      method simulateArrival (q: seq <TimedEvent>)
      // This method adds zero or more events to the queue.
         modifies sys`queue
         requires sys.validQueue (sys.queue)
         requires q == sys.queue
         ensures q <= sys.queue           // old queue is a prefix of new queue
         ensures sys.validQueue (sys.queue)

      method pickNextEvent (q: seq <TimedEvent>)
         modifies sys, sys`lastTime, prog`generatedEvents, prog
         modifies prog.globals
         requires prog.sys == this.sys
         requires prog.generatedEvents == {}
         requires sys.validQueue (sys.queue)
         requires |sys.queue| > 0
         requires q == sys.queue
         requires prog.globals.parameterConstraints ()
         requires prog.globals.stateInvariant (q[0].time, q[0].timestamp, sys.lastTime)
         requires (sys.time == q[0].time && sys.timestamp == q[0].timestamp) <==> prog.globals.stateInvariant (q[0].time , q[0].timestamp, sys.lastTime)
         requires prog.operatingAssumptions (q[0].event, q[0].time, q[0].timestamp, sys.lastTime)
         ensures sys.validQueue (sys.queue)
         ensures ( |sys.queue| == |q| - 1 ) || ( |sys.queue| == |q| )
         ensures prog.sys == this.sys
      { 
         assert prog.globals.stateInvariant (q[0].time, q[0].timestamp, sys.lastTime);
         sys.time := q[0].time;
         sys.timestamp := q[0].timestamp;
         assert prog.globals.stateInvariant (sys.time, q[0].timestamp, sys.lastTime);

         // sys.timestamp := q[0].timestamp;         
         prog.dispatch(q[0].event);
         sys.lastTime := 0;
         // if an event for recirculation was generated, add it to the queue
         sys.queue := q;
         assert |sys.queue| > 0;
         while |prog.generatedEvents| > 0
            modifies prog`generatedEvents
            modifies sys`queue
            invariant |sys.queue| > 0
            invariant sys.validQueue(sys.queue)
         {
            assert |sys.queue| > 0;
            var generatedEvent :| generatedEvent in prog.generatedEvents;
            if (generatedEvent.ports == {}) { // recirc event, add to queue
               var recircEvent: TimedEvent := generateRecircEvent(generatedEvent.event);
               sys.queue := sys.queue + [recircEvent];
            }
            prog.generatedEvents := prog.generatedEvents - {generatedEvent};
         }
         sys.queue := q[1..];
         // lastTime := q[0].time; 
         sys.lastTime := q[0].time;
      }

      method generateRecircEvent (e: Event) returns 
                                                  (recircEvent: TimedEvent)
         requires sys.validQueue (sys.queue)
         requires |sys.queue| > 0              // because method is called just
                    // after dispatch, when dispatched event still in queue
         ensures recircEvent.time > sys.queue[|sys.queue|-1].time
         ensures recircEvent.timestamp == recircEvent.time % sys.T
         ensures unchanged(this`sys)
      {
         var recircTimestamp: uint8;
         recircTimestamp := (sys.queue[|sys.queue|-1].timestamp + 1) % sys.T;
         recircEvent := 
                   TimedEvent(e, sys.queue[|sys.queue|-1].time+1, recircTimestamp);
      }

   }

   class Globals {
      constructor ()
         ensures fresh(this)

      ghost predicate stateInvariant (time: nat, timestamp: uint8, lastTime : nat)  
         reads this
      ghost predicate parameterConstraints ()          // define in program


   }

   class Program {
      var sys : Sys
      var globals : Globals
      var generatedEvents : set<GeneratedEvent>  // the event generated for recirc

      // ghost predicate parameterConstraints ()          // define in program
      //    reads {this} - {sys}
      // ghost predicate stateInvariant (time: nat, timestamp: uint8, lastTime:nat)
      //    reads {this} - {sys}                                    // define in program
      ghost predicate operatingAssumptions (event: Event, time : nat, timestamp: uint8, lastTime:nat)     
         reads this`globals, this.globals

      constructor ()                                   // define in program
         ensures sys.validQueue (sys.queue)
         ensures fresh(sys)
         ensures fresh(globals)
         ensures fresh(this)
         {
            sys := new Sys();
            globals := new Globals();
         }

      method dispatch (e: Event)
         modifies globals                                          // define in program
         modifies this`generatedEvents
         requires sys.timestamp == sys.time % sys.T
         requires globals.parameterConstraints ()
         requires globals.stateInvariant (sys.time, sys.timestamp, sys.lastTime)
         requires operatingAssumptions (e, sys.time, sys.timestamp, sys.lastTime)
         requires generatedEvents == {}
         ensures unchanged(this`sys)

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

   import opened ParseUtils
   class Parser {
      static ghost predicate validPacket(p:Packet) 
      static ghost predicate parserSpecification(p : Packet, d : ParseDecision<Event>) 
         requires validPacket(p)
      static function parse(p : Packet) : ParseDecision<Event>
         requires p.offset == 0
         requires validPacket(p) 
         ensures (parserSpecification(p, parse(p)))
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
