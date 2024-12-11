/*-------------------------------------------------------------------------
SINGLE-SWITCH ALGORITHM AND ITS SPECIFICATION (verified)

This is the algorithm to be implemented for protection against DNS
reflection attacks, in its most abstract and readable form.
-------------------------------------------------------------------------*/
// NEW: Parser class implementation and test
include "baseTest.dfy"

module LucidProg refines LucidBase {
   import opened IntTypes

   datatype Event =
    | ProcessPacket (dnsRequest: bool, uniqueSig: uint16)
    | SimulatedClockTick ()
    | SimulatedHardwareFailure ()

class Program ... {

   // Parameters
   const I : nat := 16                                   // interval length
   const Q : nat := 10                         // maximum DNS response time
   const Roff : nat := 20      // observation window for stopping filtering
   const U : nat := 2                              // upper count threshold
   const L : nat := 1                              // lower count threshold

   // Address State
   var currentIntv : nat                            // the current interval
   var count : nat                               // counter for DNS replies
   var filtering : bool              // turns adaptive filtering on and off
   var timeOn : nat               // effective time filtering was turned on
   var requestSet : set <nat>            // pending requests, for filtering
   var actualTimeOn : nat          // actual time filtering turned on
   var preRequestSet : set <nat>       // requestSet, before deletion
   var forwarded : bool                 // fate of the current packet

   predicate parameterConstraints ()          // ghost, from problem domain
      {  Roff > I > 0 && Q > 0  }

   constructor ()
      ensures validQueue (queue)
      ensures parameterConstraints ()
      ensures stateInvariant (0)
   {
      queue := [];
      filtering, forwarded := false, false;
      currentIntv, count, timeOn, actualTimeOn := 0, 0, 0, 0;
      requestSet := {};
   }

   predicate protecting (time: nat) 
      reads this
   {  filtering && (time - actualTimeOn) >= Q  }

   predicate protectImplmnt (time: nat) 
      reads this
   {  filtering && (time - timeOn) >= Q  }

   predicate stateInvariant (time: nat)
   {  (actualTimeOn <= timeOn)
   && (timeOn <= time)  
   && ((timeOn > actualTimeOn) ==> (time >= timeOn + Q))
   && (filtering ==> (protecting (time) <==> protectImplmnt (time)))
   && (! filtering ==> requestSet == {})
   } 

   method dispatch (e: TimedEvent) 
   {
      if
         case e.event.ProcessPacket? => 
            {  processPacket 
                  (e.time, e.event.dnsRequest, e.event.uniqueSig);  
               assert stateInvariant (e.time);
               assert forall i :: i >= e.time ==> stateInvariant (i);
            }
         case e.event.SimulatedClockTick? => 
            {  simulatedClockTick (e.time);  
               assert stateInvariant (e.time);
               assert forall i :: i >= e.time ==> stateInvariant (i);
            }
         case e.event.SimulatedHardwareFailure? => 
            {  simulatedHardwareFailure (e.time);  
               assert stateInvariant (e.time);
               assert forall i :: i >= e.time ==> stateInvariant (i);
            }
         assert stateInvariant (e.time);
         assert forall i :: i >= e.time ==> stateInvariant (i);
   }

   method processPacket (time: nat, dnsRequest: bool, uniqueSig: nat) 
      modifies this
      requires parameterConstraints ()
      requires stateInvariant (time)
      ensures forwarded ==> 
              (  dnsRequest || ! protecting (time) 
              || uniqueSig in preRequestSet       )  // Adaptive Protection
      ensures ! forwarded ==>                  
              (  ! dnsRequest && protecting (time)
              && ! (uniqueSig in preRequestSet)   )         // Harmlessness
      ensures stateInvariant (time)
      ensures unchanged(this`queue)
      ensures forall i :: i >= time ==> stateInvariant (i)
   {
      if (dnsRequest) {  processRequest (time, uniqueSig); }
      else {  processReply (time, uniqueSig); }
   }

   method processRequest (time: nat, uniqueSig: nat)
      modifies this
      requires parameterConstraints ()
      requires stateInvariant (time)
      ensures forwarded
      ensures stateInvariant (time)
      ensures unchanged(this`queue)
   {
      if (filtering) {  requestSet := requestSet + { uniqueSig }; }
      forwarded := true;                                    // ghost update
   }

   function interval (time: nat) : nat
      reads this
      requires parameterConstraints ()
   {  time / I  }

   function creditedProtectingTime (time: nat) : int
      reads this
   {  time - (timeOn + Q)  }

   method processReply (time: nat, uniqueSig: nat) 
      modifies this
      requires parameterConstraints ()
      requires stateInvariant (time)
      ensures forwarded ==>                     
              (  ! protecting (time) || uniqueSig in preRequestSet  )   
      ensures ! forwarded ==>            
              (  protecting (time) && ! (uniqueSig in preRequestSet)  )    
      ensures stateInvariant (time)
      ensures unchanged(this`queue)
   {
      preRequestSet := requestSet;                          // ghost update
   // Changes to measurement state:
   // If an interval boundary has been crossed, save the count in
   // oldCount, and reset the counter to 1 (for this reply).  Otherwise
   // simply increment the count.
   // If there is an interval with no reply packets, then the count
   // will not be reset for that interval.  However, the count will
   // never include replies from more than one interval.
      var oldCount : nat := 0;
      if interval (time) != currentIntv {
         oldCount := count;
         count := 1;
         currentIntv := interval (time);
      }
      else {  count := count + 1; }

   // Changes to filtering state:
   // Turning filtering on:
   // Filtering is turned on as soon as count reaches upper threshold.
   // (Note that in !filtering test of count, it should never exceed U, so
   // this is defensive programming.)
      if ! filtering {
         if count >= U {
            filtering := true;
            timeOn := time;
            actualTimeOn := time;                           // ghost update
         }
      assert count >= U ==> filtering;    // Attack Response (partial spec)
      }
   // Turning filtering off:
   // Consider the case that once protecting begins, the count in each
   // interval is less than L.  Then timeOn == actualTimeOn, and as soon as
   // Roff time has elapsed, filtering can be turned off.  Now consider
   // the case in which protecting has begun, and the count in an interval
   // is high.  In this case timeOn is reset to what it would be if 
   // protecting had just become true.  Now there is no chance to turn 
   // filtering off until time Roff elapses with no high counts.
      else { // filtering
         if ! protectImplmnt (time) { }         // too early to do anything
         else { // time Q has elapsed, we are now protecting
            if oldCount > 0 { // interval boundary crossed 
               if (oldCount < L && creditedProtectingTime (time) >= Roff)
                  {  filtering := false;
                     requestSet := {};
                  }
               else { // checking if count is still high
                  if oldCount >= L { // count is too high, reset the
                                     // filtering clock back to the
                                     // time when protection begins
                     timeOn := time - Q;
                  }
               // count is low, just waiting for Roff to elapse
               }
               assert                            // Modified Letup Response
                  creditedProtectingTime (time) >= Roff ==> ! filtering; 
            }  // end of case where interval boundary crossed
         }  // end of protecting case
      }  // end of filtering case

   // Filtering decision:
      if protectImplmnt (time) {  filter (time, uniqueSig); }
      else {  forwarded := true; }                          // ghost update
   }

   method filter (time: nat, uniqueSig: nat) 
      modifies this
      requires protectImplmnt (time)
      requires preRequestSet == requestSet
      requires parameterConstraints ()
      requires stateInvariant (time)
      ensures forwarded ==>                          // Adaptive Protection
              (  ! protecting (time) || uniqueSig in preRequestSet  )   
      ensures ! forwarded ==>                               // Harmlessness
              (  protecting (time) && ! (uniqueSig in preRequestSet)  )    
      ensures stateInvariant (time)
      ensures unchanged(this`queue)
   {
      if uniqueSig in requestSet {
         requestSet := requestSet - { uniqueSig };
         forwarded := true;                                 // ghost update
      }
      else {  forwarded := false; }                         // ghost update
   }

   method simulatedHardwareFailure (time: nat)                     // ghost
      modifies this
      requires parameterConstraints ()
      requires stateInvariant (time)
      ensures stateInvariant (time)
      ensures unchanged(this`queue)
      ensures forall i :: i >= time ==> stateInvariant (i)
   {
      filtering, forwarded := false, false;
      currentIntv, count, timeOn, actualTimeOn := 0, 0, 0, 0;
      requestSet := {};
   }

   method simulatedClockTick (time: nat)
      modifies this
      requires parameterConstraints ()
      requires stateInvariant (time)
      ensures stateInvariant (time)
      ensures unchanged(this`queue)
      ensures forall i :: i >= time ==> stateInvariant (i)
   {
      var timePlus : nat := time + 1;
      assert stateInvariant (timePlus);
   }
}

// 
class Parser ... { 
   // Parser 
   static ghost predicate validPacket(p:Packet) 
   {
      |p.bytes| >= 44  // 14 (eth) + 20 (ipv4) + 8 (udp) + 2 (dns request id)
      && p.offset == 0 // number of bytes parsed so far. starts at 0.
   } 

   static ghost predicate parserSpecification(p : Packet, d : ParseDecision<Event>) 
   { 
      if (p.bytes[12] != 0x08 || p.bytes[13] != 00) then d.GenerateExtern?  // non-ipv4 are dropped
      else if (p.bytes[23] != 0x11) then d.GenerateExtern?                  // non-udp are dropped
      else if ((ntohs(p.bytes[34..36]) == 53))               // sport == 53 => response
         then (
            match d 
               case Generate(ProcessPacket(false, _)) => true
               case _ => false
         )
      else if ((ntohs(p.bytes[36..38]) == 53))               // dport == 53 => request
         then (
            match d 
               case Generate(ProcessPacket(true, _)) => true
               case _ => false
         )
      else d.GenerateExtern?                               // neither sport nor dport == 53 => forward 
   }

   static function parse(p : Packet) : ParseDecision<Event>  
   { 
      ghost var pre_eth := p.bytes;
      var (p, dmac) := read48(p);
      // int<48> dmac = read(48, p);
      var (p, smac) := read48(p);
      var (p, ethType) := read16(p);
      if (ethType == 0x0800) then
         var p := skip(p, 9);// skip to proto
         var (p, proto) := read8(p);
         if (proto == 0x11) then 
               var p := skip(p, 10); // skip to udp
               ghost var pre_sport := p.bytes;
               var (p, sport) := read16(p);
               ghost var pre_dport := p.bytes;
               var (p, dport) := read16(p);

               assert (pre_sport[0..2] == pre_eth[34..36]);
               assert (pre_dport[0..2] == pre_eth[36..38]);

               match (sport, dport) 
               case (53, _) =>             // case: dns response
                  assert (ntohs(pre_sport[0..2]) == 53);
                  var dnsRequest := false;
                  var p := skip(p, 4); // skip to dns
                  var (p, dnsId) := read16(p);
                  Generate(ProcessPacket(dnsRequest, dnsId))
               case (_, 53) =>               // case dns request
                  assert (ntohs(pre_sport[0..2]) != 53);
                  assert (ntohs(pre_dport[0..2]) == 53);
                  var dnsRequest := true;
                  var p := skip(p, 4); // skip to dns
                  var (p, dnsId) := read16(p);
                  Generate(ProcessPacket(dnsRequest, dnsId))
               case (_, _) =>                   // case: non-dns
                  assert (ntohs(pre_sport[0..2]) != 53);
                  assert (ntohs(pre_dport[0..2]) != 53);
                  //  assert (pre_sport[0..2] == pre_eth[34..36]);
                  //  assert (pre_dport[0..2] == pre_eth[36..38]);
                  assert (ntohs(pre_eth[34..36]) != 53);
                  assert (ntohs(pre_eth[36..38]) != 53);
                  GenerateExtern("ForwardEth", [dmac, smac]) 
         else  
               GenerateExtern("ForwardEth", [dmac, smac])      // not udp: forward
      else
         GenerateExtern("ForwardEth", [dmac, smac])         // not ipv4: forward
   }
}



}

import opened LucidProg
import opened IntTypes
import opened ParseUtils

method printState (prog : Program)
{
   print "filtering: ", prog.filtering, 
         "   forwarded: ", prog.forwarded, "\n";
   print "currentIntv: ", prog.currentIntv, 
         "   actualTimeOn: ", prog.actualTimeOn, 
         "   timeOn: ", prog.timeOn, "\n";
}

method NoParserTest ()
// To run a test, you must define the constants inline.
// To run a test, initialize the queue with your test events, as shown
//    below.
//    In TimedEvent (ProcessPacket(false,31),20),
//       false = DNS reply, 31 = uniqueSig, 20 = time
// Currently simulateArrivals is not defined.  This does not seem to
//    prohibit execution.
{
   var prog := new Program ();
   var maxSteps := 10;              // set maximum number of events handled
                                                      // expect !filtering
   prog.queue :=     // initialize queue
        [ TimedEvent (ProcessPacket(false,31),20) ]   // expect forwarded,
                                                         // currentI = 1
      + [ TimedEvent (ProcessPacket(true,32),24) ]    // expect forwarded,
                                                         // sig !stored,
                                                         // filtering,
                                                         // timeOn = 24,
                                                         // actualTO = 24
      + [ TimedEvent (ProcessPacket(false,33),28) ]   // expect forwarded
      + [ TimedEvent (ProcessPacket(true,34),30) ]    // expect forwarded,
                                                         // sig stored
      + [ TimedEvent (ProcessPacket(false,35),36) ]   // expect !forwarded,
                                                         // currentI = 2
      + [ TimedEvent (ProcessPacket(false,34),40) ]   // expect forwarded,
                                                         // timeOn = 30
      + [ TimedEvent (ProcessPacket(true,36),52) ]    // expect forwarded,
                                                         // sig stored,
                                                         // currentI = 3
      + [ TimedEvent (ProcessPacket(false,34),70) ]   // expect !forwarded,
                                                         // currentI = 4
      + [ TimedEvent (ProcessPacket(false,36),87) ];  // expect forwarded,
                                                         // currentI = 5,
                                                         // !filtering,
   if (  prog.validQueue (prog.queue) 
      && prog.stateInvariant (prog.queue[0].time)  )  {
      while (maxSteps > 0) 
         invariant 
            prog.validQueue (prog.queue) 
         && (|prog.queue| > 0 ==> prog.stateInvariant (prog.queue[0].time))
      {
         if |prog.queue| > 0 {  
            prog.pickNextEvent (prog.queue);  
            printState(prog);
         }
         prog.simulateArrivals (prog.queue);
         maxSteps := maxSteps - 1;
      }
   }
   else {  print "Initial queue or state is not valid.\n"; }
}




method serializeEvent(e : Event) returns (pkt : Packet)
   // serialize an event to a Packet
   ensures Parser.validPacket(pkt) 
{
   var eth_dst : seq<uint8> := [0x0, 0x1, 0x2, 0x3, 0x4, 0x5];
   var eth_src : seq<uint8> := [0x6, 0x7, 0x8, 0x9, 0xa, 0xb];
   var eth_ty  : seq<uint8> := htons(0x0800);
   var eth_hdr : seq<uint8> := eth_dst + eth_src + eth_ty;
   var ip_hdr  : seq<uint8> := seq(9, _ => 0x0) + [0x11] + seq(10, _ => 0x0); // udp proto
   var misc_udp_port : seq<uint8> := [0x11, 0x22]; // a random udp port 
   var udp_csum : seq<uint8> := seq(4, _ => 0x0); // blank padding after udp ports

   match e {
      case ProcessPacket(dnsRequest, uniqueSig) => 
         if (dnsRequest == true) { 
            var bytes : seq<uint8> := eth_hdr + ip_hdr            // eth + ip
               + misc_udp_port + htons(53) +  udp_csum          // udp
               + htons(uniqueSig);                              // dns    
            assert |bytes| >= 44;
            pkt := Packet(bytes, 0);
         } else
            {
            var bytes : seq<uint8> := eth_hdr + ip_hdr            // eth + ip
               + htons(53) + misc_udp_port +  udp_csum          // udp
               + htons(uniqueSig);                              // dns            
            assert |bytes| >= 44;
            pkt := Packet(bytes, 0);

         }
      case _ => pkt := Packet(seq(64, _ => 0), 0);
   }
}
method ParserTest ()
// Same as OldMain, but with parser.
{
   var prog := new Program ();
   var maxSteps := 10;              // set maximum number of events handled
                                                      // expect !filtering

   var inputEvents := [ProcessPacket(false,31), ProcessPacket(true,32), ProcessPacket(false,33), ProcessPacket(true,34), ProcessPacket(false,35), ProcessPacket(false,34), ProcessPacket(true,36), ProcessPacket(false,34), ProcessPacket(false,36)];                                                         
   // When testing with a parser, the input events are serialized into packets
   // those packets are then parsed and the resulting events are timed and
   // put into the queue.  The queue is then processed the same way as 
   // for a test without a parser.
   var packets := [];
   for i := 0 to |inputEvents|
      invariant |packets| == i
      invariant (forall i :: 0 <= i < |packets| ==> Parser.validPacket(packets[i]))
   {
      var pkt := serializeEvent(inputEvents[i]);
      assert (Parser.validPacket(pkt));
      packets := packets + [pkt];

   }
   var arrivalTimes := [20, 24, 28, 30, 36, 40, 52, 70, 87];
   // run the parser to build a seq of timedEvents
   var timedEvents : seq<TimedEvent> := [];
   var n_events := 0;
   for i := 0 to |packets| 
      invariant |timedEvents| == i
   {
      var parserDecision := Parser.parse(packets[i]);
      expect (parserDecision.Generate?); // expect correct parsing.
      var e := parserDecision.e;
      timedEvents := timedEvents + [TimedEvent(e, arrivalTimes[i])];
   }
   assert (|packets| == |timedEvents|);
   // end parser-specific test code

   // set the input queue
   prog.queue := timedEvents;
   // run the test
   if (  prog.validQueue (prog.queue) 
      && prog.stateInvariant (prog.queue[0].time)  )  {
      while (maxSteps > 0) 
         invariant 
            prog.validQueue (prog.queue) 
         && (|prog.queue| > 0 ==> prog.stateInvariant (prog.queue[0].time))
      {
         if |prog.queue| > 0 {  
            prog.pickNextEvent (prog.queue);  
            printState(prog);
         }
         prog.simulateArrivals (prog.queue);
         maxSteps := maxSteps - 1;
      }
   }
   else {  print "Initial queue or state is not valid.\n"; }
}

method Main() 
{
   print ("----------- test without parser ----------\n");
   NoParserTest();
   print("\n");
   print ("----------- test with parser ----------\n");
   ParserTest();
   print("\n");
}



/* 
There is a lot to do to finalize this testing capability.
 * discuss/fix/handle commented issues above.
 * document/note all formerly-ghost structures.
*/
