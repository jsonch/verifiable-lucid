abstract module LucidBase {

   type Event (==)

   datatype TimedEvent = TimedEvent (event: Event, time: nat)

   class Program {
      var queue : seq <TimedEvent>

      predicate parameterConstraints ()                // define in program
         reads this

      predicate stateInvariant (time: nat)             // define in program
         reads this

      predicate validQueue (q: seq <TimedEvent>)         // queue invariant
      {
         match |q| {
            case 0 => true
            case _ => forall j | 0 <= j < |q|-1 ::
                         q[j].time <= q[j+1].time  }
      }        
        
      constructor ()                                   // define in program
         ensures validQueue (queue)
         ensures parameterConstraints ()
         ensures stateInvariant (0)

      method simulateArrivals (q: seq <TimedEvent>)
         // This method adds zero or more events to the queue, and may be
         // defined in the program.  If the method is not defined, any 
         // events whatsoever can be added, provided that the queue remains
         // valid.
         // Remember: In a bounds expression [..] numbers are lengths.
         modifies this
         requires parameterConstraints ()
         requires validQueue (queue)
         requires |queue| > 0 ==> stateInvariant (queue[0].time)
         requires q == queue                 
         ensures q <= queue           // old queue is a prefix of new queue
         ensures validQueue (queue)
         ensures |queue| > 0 ==> stateInvariant (queue[0].time)
      {  }

      twostate lemma {:axiom} stateInvariantDoesNotDependOnQueue(time: nat)
         ensures old(stateInvariant(time)) == stateInvariant(time)

      method pickNextEvent (q: seq <TimedEvent>)
         modifies this
         requires parameterConstraints ()
         requires validQueue (queue)
         requires |queue| > 0
         requires stateInvariant (queue[0].time)
         requires q == queue
         ensures |queue| == |q| - 1
         ensures validQueue (queue)
         ensures |queue| > 0 ==> stateInvariant (queue[0].time) 
      {
         dispatch(q[0]);
         label before:
         this.queue := q[1..];
         if |queue| > 0 {
            stateInvariantDoesNotDependOnQueue@before(queue[0].time); }
      }

      method dispatch (e: TimedEvent)                  // define in program
         modifies this 
         requires parameterConstraints ()
         requires stateInvariant (e.time)
         ensures unchanged(this`queue)
         ensures forall i :: i >= e.time ==> stateInvariant (i)
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


module IntTypes {
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
      | GenerateExtern(name:string, args:seq<nat>)

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
