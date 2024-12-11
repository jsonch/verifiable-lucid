/*-------------------------------------------------------------------------
VERIFIABLE LUCID SIMULATION MODULE FOR REFERENCE IMPLEMENTATIONS WITH
REFINEMENT OF UNBOUNDED NUMBERS AND
REFINEMENT OF EXTERNAL DATA STRUCTURES AND
REFINEMENT OF MEMORY ACCESSES
-------------------------------------------------------------------------*/
/* Small changes (11/12/24) 
1. Added a "Types" module with fixed-width integer types to use in executable code.
1. Parsing additions: 
   1. Add a "ParseUtils" module with parsing helpers, e.g., a "Packet" class and 
      functions to read bytes from the packet into local variables.
   2. Added a "Parser" class in the LucidBase, which the programmer extends 
      to implement and verify their parser. The Parser class contains a user-defined: 
      - valid input packet predicate, 
      - parser specification, and 
      - parser implementation function.
3. Make the filtering decision (in DNSprotect.dfy) depend on timestamp, not time.
   """
   // Filtering decision:
      if tmpFiltering && (timestamp - tmpTimestampOn) % T >= Q {
         filter (time, timestamp, uniqueSig);
      }
      else {  forwarded := true; }
   """
4. Change "time" and "lastTime" into ghost parameters, 
   since the implementation does not know the unbounded time.
5. Added "bitShiftDivision" helper function to divide by a power of 2 in executable code

[todo] N. Change event generation semantics. Now: 
   - to generate a recirculation event, 
      the program calls a "generate(event)" helper, 
      rather than returning a recircCmd
   - to generate an output packet, i.e., forward, 
      the program calls a "generatePort(event)" helper, 
      rather than setting a "ports" variable.

[todo optional] N+1. Make timestamp a variable rather than passed in as an argument.
*/

module IntTypes {
   // Integer types to use in executable code
   type uint8 = x : nat | 0 <= x < 256
   type uint16 = x : nat | 0 <= x < 65536
   type uint20 = x : nat | 0 <= x < 1048576
   type uint24 = x : nat | 0 <= x < 16777216
   type uint32 = x : nat | 0 <= x < 4294967296
   type uint48 = x : int | 0 <= x < 281474976710656

   function IsPowerOf2(n: nat): bool
   { 
      if n == 0 then false
      else if n == 1 then true
      else if n % 2 != 0 then false
      else IsPowerOf2(n/2)
   }   
   function bitShiftDivision(x: nat, i: nat): nat
      // x / i, where i is a power of 2
      requires IsPowerOf2(i)
      ensures bitShiftDivision(x, i) == x / i
   {
      x / i
   }
}

abstract module LucidBase {
   import opened IntTypes
   type bits = uint8                   // bound (256) must match parameter T

   type Event (==)
   datatype TimedEvent = 
      TimedEvent (event: Event, ghost time: nat, timestamp: bits)
            
   datatype RecircCmd = RecircCmd (generate: bool, event: Event)

   class Program {
      const T : nat := 256               // number must match limit on bits
      var queue : seq <TimedEvent>
      ghost var lastTime : nat

      ghost predicate parameterConstraints ()          // define in program
         reads this

      ghost predicate stateInvariant (time: nat, timestamp: bits) // define
         reads this                                           // in program
 
      ghost predicate operatingAssumptions (e: TimedEvent)     
         reads this                                    // define in program

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

      constructor ()                                   // define in program
         ensures validQueue (queue)
         // ensures parameterConstraints ()
         ensures stateInvariant (0, 0)

      method simulateArrival (q: seq <TimedEvent>)
      // This method adds zero or more events to the queue.
         modifies this
         requires validQueue (queue)
         requires q == queue
         ensures q <= queue           // old queue is a prefix of new queue
         ensures validQueue (queue)

      method pickNextEvent (q: seq <TimedEvent>)
         modifies this
         requires validQueue (queue)
         requires |queue| > 0
         requires q == queue
         requires parameterConstraints ()
         requires stateInvariant (q[0].time, q[0].timestamp)
         requires operatingAssumptions (q[0])
         ensures validQueue (queue)
         ensures ( |queue| == |q| - 1 ) || ( |queue| == |q| )
      {
         var recirc := dispatch(q[0]);
         if recirc.generate { 
            var recircEvent:TimedEvent :=generateRecircEvent(recirc.event);
            queue := q[1..] + [recircEvent];
         }
         else {  queue := q[1..]; }
         lastTime := q[0].time;
      }

      method dispatch (e: TimedEvent) returns (recirc: RecircCmd)
         modifies this                                 // define in program
         requires e.timestamp == e.time % T
         requires parameterConstraints ()
         requires stateInvariant (e.time, e.timestamp)
         requires operatingAssumptions (e)
         ensures unchanged(this`queue) ensures unchanged(this`lastTime)

      method generateRecircEvent (e: Event) returns 
                                                  (recircEvent: TimedEvent)
         requires validQueue (queue)
         requires |queue| > 0              // because method is called just
                    // after dispatch, when dispatched event still in queue
         ensures recircEvent.time > queue[|queue|-1].time
         ensures recircEvent.timestamp == recircEvent.time % T
      {
         var recircTimestamp: bits;
         recircTimestamp := (queue[|queue|-1].timestamp + 1) % T;
         recircEvent := 
                   TimedEvent(e, queue[|queue|-1].time+1, recircTimestamp);
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


module ParseUtils {
   // Utilities to use in the parser definition
   import opened IntTypes
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
