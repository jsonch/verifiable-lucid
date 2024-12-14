/*-------------------------------------------------------------------------
VERIFIABLE LUCID TEMPLATE FOR REFERENCE IMPLEMENTATIONS WITH
REFINEMENT OF UNBOUNDED NUMBERS AND
REFINEMENT OF EXTERNAL DATA STRUCTURES AND
REFINEMENT OF MEMORY ACCESSES

This file also contains the verified implementation of the paper's case
study.
-------------------------------------------------------------------------*/
















include "lucidBase4.dfy"




































module LucidProg refines LucidBase { 
   import opened Memop 

      
   type counter = uint32              // limit must exceed U

   datatype Event =
      | ProcessPacket (dnsRequest: bool, uniqueSig: uint16)
      | ForwardPacket()
      | SimulatedClockTick ()
      | SimulatedHardwareFailure () 
      | SetFiltering (toWhat: bool)
      | Non ()

   class Globals ... {
      // Parameters 
      static const I : uint8 := 16           // interval length, < T and a power of 2
      static const Q : uint8    := 10                         // maximum DNS response time
      static const Roff : uint8  := 20        // observation window for stopping filtering
      static const U : counter   := 2                            // upper count threshold
      static const L : counter   := 1                            // lower count threshold

      // Address State
      var currentIntv : StateVar <uint8>                   // current interval
      var count : StateVar <counter>                // counter for DNS replies
      var filtering : StateVar <bool>   // turns adaptive filtering on and off
      ghost var timeOn : nat         // effective time filtering was turned on
      var timestampOn : StateVar <uint8>           // implementation of timeOn
      ghost var requestSet : set <uint16>   // pending requests, for filtering
      ghost var forwarded: bool                  // fate of the current packet
      ghost var actualTimeOn : nat          // actual time filtering turned on
      ghost var preRequestSet : set <nat>       // requestSet, before deletion
      var recircPending : StateVar <bool>   // a "semaphore" for recirculation


      constructor () 
         ensures stateInvariant (0, 0, 0)  
      {
         filtering, recircPending := Atomic (false), Atomic (false);
         timeOn, actualTimeOn := 0, 0;
         currentIntv, timestampOn, count := Atomic(0), Atomic(0), Atomic(0);
         requestSet := {};
      } 
      ghost predicate protecting (time: nat)  
         reads this
      {  filtering.val && (time - actualTimeOn) >= Q as nat  }

      ghost predicate protectImplmnt (timestamp: uint8)
         reads this
      {  filtering.val && elapsedTime (timestamp, timestampOn.val) >= Q  }

      function elapsedTime (now: uint8, origin: uint8): (res: uint8)
         reads this
         // Function satisfies specification because of mod arithmetic.
            ensures now >= origin ==> res == (now - origin)
            ensures now < origin ==>                        // 0 is T as uint8
               res == (now + Sys.T - origin)
      {  (now - origin) % Sys.T  }        // implemented as bit-vector subtraction

      ghost predicate stateInvariant (time: nat, timestamp: uint8, lastTime : nat)
      {  (  timestampOn.val == timeOn % Sys.T  )
      && (  actualTimeOn <= timeOn  )
      && (  timeOn <= time  )
      && (  (timeOn > actualTimeOn) ==> (time >= timeOn + Q as nat)  )
      && (  filtering.val ==> 
               (protecting (time) <==> protectImplmnt (timestamp)))
      && (  ! filtering.val ==> requestSet == {}  ) 
      }



   }

   class Program ... { 

      // constructor ()
      //    // ensures parameterConstraints ()
      //    ensures globals.stateInvariant (0, 0, 0) 
      // {
      //    filtering, recircPending := Atomic (false), Atomic (false);
      //    timeOn, actualTimeOn := 0, 0;
      //    currentIntv, timestampOn, count := Atomic(0), Atomic(0), Atomic(0);
      //    requestSet := {};
      // } 

      ghost predicate protecting (time: nat)  
         reads this
         reads globals
      {  globals.filtering.val && (time - globals.actualTimeOn) >= globals.Q as nat  }

      ghost predicate protectImplmnt (timestamp: uint8)
         reads this
         reads globals
      {  globals.filtering.val && elapsedTime (timestamp, globals.timestampOn.val) >= globals.Q  }

      function elapsedTime (now: uint8, origin: uint8): (res: uint8)
         reads this
         // Function satisfies specification because of mod arithmetic.
            ensures now >= origin ==> res == (now - origin)
            ensures now < origin ==>                        // 0 is T as uint8
               res == (now + sys.T - origin)
      {  (now - origin) % sys.T  }        // implemented as bit-vector subtraction


      ghost predicate operatingAssumptions (event: Event, time : nat, timestamp : uint8, lastTime:nat) 
      // There cannot be restrictions on recirculation events, i.e.,
      // SetFiltering events, because they were already chosen by the program.
      {
         if      event.ProcessPacket?
         then       (globals.filtering.val ==> time < globals.actualTimeOn + Sys.T) 
               && (time - lastTime < Sys.T - Globals.I              ) 
         else if event.SimulatedClockTick?
         then    (globals.filtering.val ==> (time + 1) < globals.actualTimeOn + Sys.T) 
         else true
      }  

      method dispatch (e : Event) 
         {  
            if {
               case e.ProcessPacket? => 
               {  processPacket 
                     (e.dnsRequest, e.uniqueSig);
               }
               case e.SetFiltering? => 
                  setFiltering (e.toWhat);
               case e.SimulatedClockTick? =>
                  simulatedClockTick ();
               case e.SimulatedHardwareFailure? => 
                  simulatedHardwareFailure ();
               case e.Non? => 
               case e.ForwardPacket? => 
            }
         } 

      method processPacket (dnsRequest: bool, 
                                 uniqueSig: uint16)
         modifies globals
         modifies this`generatedEvents
         requires generatedEvents == {}
         requires sys.timestamp == sys.time % sys.T
         requires globals.parameterConstraints ()
         requires globals.stateInvariant (sys.time, sys.timestamp, sys.lastTime)
         // There must be a packet between any two interval rollovers, so
         // that interval boundaries can be detected.  Unfortunately, the
         // specification is not strong enough to cause verification to fail
         // without this operating assumption.
            requires sys.time - sys.lastTime < sys.T - globals.I
         // Below is the operating assumption to make attack time spans 
         // measurable.
            requires globals.filtering.val ==> sys.time < globals.actualTimeOn + sys.T
         // The following is Adaptive Protection, can ONLY be verified when
         // the request set is implemented exactly.
         // Probabilistic Adaptive Protection means that Adaptive Protection
         // holds only in the likely cases where the positive from the Bloom
         // filter is true.
         ensures globals.forwarded ==>                          // Adaptive Protection
               (  dnsRequest || ! protecting (sys.time)   
               || uniqueSig in globals.preRequestSet       )
         ensures ! globals.forwarded ==>
               (  ! dnsRequest && protecting (sys.time)
               && ! (uniqueSig in globals.preRequestSet)   )         // Harmlessness
         ensures globals.stateInvariant (sys.time, sys.timestamp, sys.lastTime)
         ensures unchanged(this`sys)

      {
         if dnsRequest {  
            processRequest (uniqueSig);
            generate_port(1, ProcessPacket(dnsRequest, uniqueSig));
         }
         else {   
            var allowPacket := processReply (uniqueSig);
            if (allowPacket) {  
               generate_port(1, ProcessPacket(dnsRequest, uniqueSig)); 
            }
         }   
      } 

      method processRequest (uniqueSig: uint16)
         modifies globals
         requires sys.timestamp == sys.time % sys.T
         requires globals.parameterConstraints ()
         requires globals.stateInvariant (sys.time, sys.timestamp, sys.lastTime)
         ensures globals.forwarded
         ensures globals.stateInvariant (sys.time, sys.timestamp, sys.lastTime)
         ensures unchanged(this`sys)
      {
         var tmpFiltering : bool := Get (globals.filtering, nocalc, true);
         if tmpFiltering {
            bloomFilterInsert (uniqueSig);
            globals.requestSet := globals.requestSet + { uniqueSig };          // ghost update
         }
         globals.forwarded := true; 
      }

      function interval (timestamp: uint8): uint8
         reads this`globals
         requires globals.parameterConstraints ()
      {  timestamp / globals.I  }                    // implemented with a right-shift
   
      function upperBoundedIncr (count: counter, unused: counter) : counter
      // this is a custom memcalc
      {  if count < Globals.U then (count + 1) else (count)  }

      function newTime (memVal: uint8, timestamp: uint8): uint8
      // this is a custom memcalc
      {  if (timestamp - memVal) % Sys.T >= Globals.Q then (timestamp - Globals.Q) % Sys.T
         else memVal
      }

      ghost function creditedProtectingTime (time: nat) : int
         reads this`globals
         reads globals`timeOn
      {  time - (globals.timeOn + Globals.Q)  }

      method processReply (uniqueSig: uint16)  
         returns (allowPacket : bool)
         modifies globals
         modifies this`generatedEvents
         requires generatedEvents == {}
         requires sys.timestamp == sys.time % sys.T
         // There must be a packet between any two interval rollovers, so
         // that interval boundaries can be detected.  Unfortunately, the
         // specification is not strong enough to cause verification to fail
         // without this operating assumption.
            requires sys.time - sys.lastTime < sys.T - globals.I
         // Operating assumption to make attack time spans measurable.
            requires globals.filtering.val ==> sys.time < globals.actualTimeOn + sys.T
         requires globals.parameterConstraints ()
         requires globals.stateInvariant (sys.time, sys.timestamp, sys.lastTime)     
         // Adaptive Protection, requires exact request set
            ensures globals.forwarded ==>                 
               (  ! protecting (sys.time) || uniqueSig in globals.preRequestSet )
         ensures ! globals.forwarded ==>                               // Harmlessness
               (  protecting (sys.time) && ! (uniqueSig in globals.preRequestSet) ) 
         ensures globals.stateInvariant (sys.time, sys.timestamp, sys.lastTime)
         ensures unchanged(this`sys)
      {  

         globals.preRequestSet := globals.requestSet;                          // ghost update
      // Changes to measurement state:
      // If an interval boundary has been crossed, save the count in
      // oldCount, and reset the counter to 1 (for this reply).  Otherwise
      // simply increment the count.
      // If there is an interval with no reply packets, then the count
      // will not be reset for that interval.  However, the count will
      // never include replies from more than one interval.
         var oldCount : counter := 0;                               
         var tmpCurrentIntv : uint8;
         var tmpCount : counter;
         tmpCurrentIntv, globals.currentIntv := GetSet (
            globals.currentIntv, nocalc, 0, swapcalc, interval (sys.timestamp) );
         if interval (sys.timestamp) != tmpCurrentIntv {
            oldCount,globals.count := GetSet ( globals.count, nocalc, 0, swapcalc, 1 );
            tmpCount := 1;
         assert globals.count.val > 0;                                          
         }
         else {
            var oldCt := globals.count.val;
            tmpCount, globals.count := GetSet (globals.count, upperBoundedIncr, 0,
                                             upperBoundedIncr, 0);
            
         assert globals.count.val > 0;                                          

         }
         assert globals.count.val > 0;                                          
         assert (oldCount > 0) ==> (globals.currentIntv.val != tmpCurrentIntv);

      // Changes to filtering state:
      // Turning filtering on:
      // Filtering is turned on as soon as count reaches upper threshold.
      // (Note that in !filtering test of count, it should never exceed U, so
      // this is defensive programming.)
         var tmpFiltering : bool := Get (globals.filtering, nocalc, true);
         var tmpTimestampOn : uint8;
         if ! tmpFiltering {
            tmpTimestampOn := Get (globals.timestampOn, nocalc, 0);
            if tmpCount >= globals.U { // time to turn filtering on
               var tmpRecircPending : bool;
               tmpRecircPending, globals.recircPending := GetSet (
                  globals.recircPending, nocalc, true, swapcalc, true);
               if ! tmpRecircPending {
                  generate(SetFiltering(true));
               }
               // else recirc already generated, do nothing
               else { } //recirc := RecircCmd (false, Non()); 
            }
            else { } // recirc := RecircCmd (false, Non()); 
            assert globals.count.val >= globals.U ==>        // Attack Response (partial spec)
                  (  globals.recircPending.val 
                  || generatedEvents == {Event(SetFiltering(true), {})});
            // assert count.val < U ==> generatedEvent == None();
         }
      // Turning filtering off:
      // Consider the case that once protecting begins, the count in each
      // interval is less than L.  Then timeOn == actualTimeOn, and as soon as
      // QRoff time has elapsed, filtering can be turned off.  Now consider
      // the case in which protecting has begun, and the count in an interval
      // is high.  In this case timeOn is reset to what it would be if 
      // protecting had just become true.  Now there is no chance to turn 
      // filtering off until time Qroff elapses with no high counts.
         else { // filtering
            if oldCount > 0 { // interval boundary crossed
               if oldCount >= globals.L {
                  ghost var oldTimestampOn := globals.timestampOn.val;        // ghost
                  tmpTimestampOn, globals.timestampOn := GetSet (
                     globals.timestampOn, newTime, sys.timestamp, newTime, sys.timestamp);
                  if oldTimestampOn != tmpTimestampOn { 
                     globals.timeOn := sys.time - globals.Q;                       // ghost update
                  }
                  // recirc := RecircCmd (false, Non());
               }
               else { // oldCount < L
                  tmpTimestampOn := Get (globals.timestampOn, nocalc, 0);
                  if (sys.timestamp - tmpTimestampOn) % sys.T >= globals.Q + globals.Roff {
                     // time to turn filtering off
                     var tmpRecircPending : bool;
                     tmpRecircPending, globals.recircPending := GetSet (
                        globals.recircPending, nocalc, true, swapcalc, true);
                     if ! tmpRecircPending {
                        generate(SetFiltering(false));
                        // recirc := RecircCmd (true, SetFiltering(false));
                     }
                     // else recirc already generated, do nothing
                     else {  } // recirc := RecircCmd (false, Non());  }
                  }
               // count is low, just waiting for QRoff to elapse
               // recirc := RecircCmd (false, Non());
               }
               assert                               // Modified Letup Response
               creditedProtectingTime (sys.time) >= globals.Roff as int ==> 
                  (  globals.recircPending.val 
                  || generatedEvents == {Event(SetFiltering(true), {})}); 
                  //recirc == RecircCmd (true, SetFiltering(true))  );
            }  // end of case where interval boundary crossed
            else {  tmpTimestampOn := Get (globals.timestampOn, nocalc, 0);}
                  // recirc := RecircCmd (false, Non());           }
         }  // end of filtering case

      // Filtering decision:
         if tmpFiltering && (sys.timestamp - tmpTimestampOn) % sys.T >= globals.Q {
            allowPacket := filter (uniqueSig);
         }
         else { globals.forwarded := true; allowPacket := true; }
      }

      method filter (uniqueSig: nat) 
         returns (allowPacket: bool)
         modifies globals
         requires sys.timestamp == sys.time % sys.T
         requires protectImplmnt (sys.timestamp)
         requires globals.preRequestSet == globals.requestSet
         requires globals.parameterConstraints ()
         requires globals.stateInvariant (sys.time, sys.timestamp, sys.lastTime)
         ensures globals.forwarded ==>  // Adaptive Protection, needs exact requestSet
                              uniqueSig in globals.preRequestSet
         ensures ! globals.forwarded ==> !(uniqueSig in globals.preRequestSet) // Harmlessness
         ensures protecting (sys.time)
         ensures globals.stateInvariant (sys.time, sys.timestamp, sys.lastTime)
         ensures unchanged(this`sys)
      { 
         allowPacket := bloomFilterQuery (uniqueSig);
         globals.forwarded := allowPacket;
         if globals.forwarded {                 // if positive is false, has no effect
            globals.requestSet := globals.requestSet - { uniqueSig };          // ghost update
         }
      }

      method setFiltering (toWhat: bool)  
         modifies globals
         requires sys.timestamp == sys.time % sys.T
         requires globals.parameterConstraints ()
         requires globals.stateInvariant (sys.time, sys.timestamp, sys.lastTime)
         ensures unchanged(this`sys)
         ensures globals.stateInvariant (sys.time, sys.timestamp, sys.lastTime)
      { 
         globals.filtering := Set (globals.filtering, swapcalc, toWhat);
         if toWhat {
            globals.timestampOn := Set (globals.timestampOn, swapcalc, sys.timestamp);
            globals.timeOn := sys.time;                                    // ghost update
            globals.actualTimeOn := sys.time;                              // ghost update
         }
         else {  globals.requestSet := {}; }                           // ghost update
         globals.recircPending := Set (globals.recircPending, swapcalc, false);
      }

      method simulatedHardwareFailure ()    // ghost
         modifies globals
         requires sys.timestamp == sys.time % sys.T
         requires globals.parameterConstraints ()
         requires globals.stateInvariant (sys.time, sys.timestamp, sys.lastTime)
         ensures unchanged(this`sys)
         ensures globals.stateInvariant (sys.time, sys.timestamp, sys.lastTime)
      {
         globals.filtering, globals.recircPending := Atomic (false), Atomic (false);
         globals.timeOn, globals.actualTimeOn := 0, 0;
         globals.currentIntv, globals.timestampOn, globals.count := Atomic(0), Atomic(0), Atomic(0);
         globals.requestSet := {};
      }  

      method simulatedClockTick ()          // ghost
         requires sys.timestamp == sys.time % sys.T
         requires globals.parameterConstraints ()
         requires globals.stateInvariant (sys.time, sys.timestamp, sys.lastTime)
         // Operating assumption to make attack time spans measurable.  
         // Without the "+ 1", the method cannot be verified.
            requires globals.filtering.val ==> (sys.time + 1) < globals.actualTimeOn + sys.T
         ensures unchanged(this`sys)
         ensures globals.stateInvariant (sys.time, sys.timestamp, sys.lastTime)
      { 
         var timePlus : nat := sys.time + 1;
         var timestampPlus : uint8 := (sys.timestamp + 1) % sys.T;
         assert globals.stateInvariant (timePlus, timestampPlus, sys.lastTime);
      }

      method {:extern}{:axiom} bloomFilterInsert (uniqueSig: nat)

      method {:extern}{:axiom} bloomFilterQuery (uniqueSig: nat)
                                                   returns (inSet: bool)
      // No false negatives:
      // A sliding-window Bloom filter automatically deletes set members
      // shortly after a guaranteed tenancy W.  You might imagine that
      // this would be a source of false negatives.  However, it is not,
      // because a request never needs to stay in the set longer than Q,
      // where Q <= W.
         ensures uniqueSig in globals.requestSet ==> inSet
      // No false positives:
      // Not true, but used to prove Adaptive Protection as a sanity
      // check.  (If deleted, Adaptive Protection cannot be proved.)  This
      // property can be false for two reasons: (1) it is the nature of
      // a Bloom filter to yield false positives sometimes; (2) in a
      // sliding-window Bloom filter, there are no timely deletions, just
      // scheduled timeouts which can be delayed.
         ensures ! (uniqueSig in globals.requestSet) ==> (! inSet)
   }


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
                     GenerateExtern("ForwardUdp")
            else 
                  GenerateExtern("ForwardIp")      // not udp: forward
         else
            GenerateExtern("ForwardEth")         // not ipv4: forward
      }
   }


}
