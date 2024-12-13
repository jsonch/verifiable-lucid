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
   
   type counter = uint20              // limit must exceed U

   datatype Event =
    | ProcessPacket (dnsRequest: bool, uniqueSig: nat)
    | SimulatedClockTick ()
    | SimulatedHardwareFailure ()
    | SetFiltering (toWhat: bool)
    | Non ()

class Program ... {

   // Parameters 
   const I : bits := 16            // interval length, < T and a power of 2
   const Q : bits                              // maximum DNS response time
   const Roff : bits           // observation window for stopping filtering
   const U : counter                               // upper count threshold
   const L : counter                               // lower count threshold

   // Address State
   var currentIntv : StateVar <bits>                    // current interval
   var count : StateVar <counter>                // counter for DNS replies
   var filtering : StateVar <bool>   // turns adaptive filtering on and off
   ghost var timeOn : nat         // effective time filtering was turned on
   var timestampOn : StateVar <bits>            // implementation of timeOn
   ghost var requestSet : set <nat>      // pending requests, for filtering
   ghost var actualTimeOn : nat          // actual time filtering turned on
   ghost var preRequestSet : set <nat>       // requestSet, before deletion
   var recircPending : StateVar <bool>   // a "semaphore" for recirculation

   ghost predicate parameterConstraints ()           // from problem domain
      {  Roff > I > 0 && Q > 0 && 0 < U < L < 1048576  }

   constructor () 
      ensures validQueue (queue) 
      // ensures parameterConstraints ()
      ensures stateInvariant (0, 0)
   {
      queue := [];
      lastTime := 0;
      filtering, recircPending := Atomic (false), Atomic (false);
      timeOn, actualTimeOn := 0, 0;
      currentIntv, timestampOn, count := Atomic(0), Atomic(0), Atomic(0);
      requestSet := {};
   }

   ghost predicate protecting (time: nat) 
      reads this
   {  filtering.val && (time - actualTimeOn) >= Q as nat  }

   ghost predicate protectImplmnt (timestamp: bits)
      reads this
   {  filtering.val && elapsedTime (timestamp, timestampOn.val) >= Q  }

   function elapsedTime (now: bits, origin: bits): (res: bits)
      reads this
      // Function satisfies specification because of mod arithmetic.
         ensures now >= origin ==> res == (now - origin)
         ensures now < origin ==>                         // 0 is T as bits
            res == (now + T - origin)
   {  (now - origin) % T  }        // implemented as bit-vector subtraction

   ghost predicate stateInvariant (time: nat, timestamp: bits)
   {  (  timestampOn.val == timeOn % T  )
   && (  actualTimeOn <= timeOn  )
   && (  timeOn <= time  )
   && (  (timeOn > actualTimeOn) ==> (time >= timeOn + Q as nat)  )
   && (  filtering.val ==> 
            (protecting (time) <==> protectImplmnt (timestamp)))
   && (  ! filtering.val ==> requestSet == {}  )
   }

   ghost predicate operatingAssumptions (e: TimedEvent) 
   // There cannot be restrictions on recirculation events, i.e.,
   // SetFiltering events, because they were already chosen by the program.
   {
      if      e.event.ProcessPacket?
      then       (filtering.val ==> e.time < actualTimeOn + T) 
              && (e.time - lastTime < T - I              ) 
      else if e.event.SimulatedClockTick?
      then    (filtering.val ==> (e.time + 1) < actualTimeOn + T) 
      else true
   }

method dispatch (e: TimedEvent) returns (recirc: RecircCmd) 
   {  
      recirc := RecircCmd (false, Non());
      if {
         case e.event.ProcessPacket? => 
         {  recirc := processPacket 
               (e.time,e.timestamp, e.event.dnsRequest, e.event.uniqueSig);
         }
         case e.event.SetFiltering? => 
            setFiltering (e.time, e.timestamp, e.event.toWhat);
         case e.event.SimulatedClockTick? => 
            simulatedClockTick (e.time, e.timestamp);
         case e.event.SimulatedHardwareFailure? => 
            simulatedHardwareFailure (e.time, e.timestamp);
         case e.event.Non? => 
      }
   } 

   method processPacket (ghost time: nat, timestamp: bits, dnsRequest: bool, 
                                uniqueSig: nat) returns (recirc: RecircCmd)
      modifies this
      requires forwarded == false // CHANGE
      requires timestamp == time % T
      requires parameterConstraints ()
      requires stateInvariant (time, timestamp)
      // There must be a packet between any two interval rollovers, so
      // that interval boundaries can be detected.  Unfortunately, the
      // specification is not strong enough to cause verification to fail
      // without this operating assumption.
         requires time - lastTime < T - I
      // Below is the operating assumption to make attack time spans 
      // measurable.
         requires filtering.val ==> time < actualTimeOn + T
      // The following is Adaptive Protection, can ONLY be verified when
      // the request set is implemented exactly.
      // Probabilistic Adaptive Protection means that Adaptive Protection
      // holds only in the likely cases where the positive from the Bloom
      // filter is true.
      ensures forwarded ==>                          // Adaptive Protection
              (  dnsRequest || ! protecting (time)   
              || uniqueSig in preRequestSet       )
      ensures ! forwarded ==>
              (  ! dnsRequest && protecting (time)
              && ! (uniqueSig in preRequestSet)   )         // Harmlessness
      ensures stateInvariant (time, timestamp)
      ensures unchanged(this`queue) ensures unchanged(this`lastTime)
   {
      if dnsRequest {  
         processRequest (time, timestamp, uniqueSig);
         recirc := RecircCmd (false, Non()); 
      }
      else {  recirc := processReply (time, timestamp, uniqueSig); }   
   }

   method processRequest (ghost time: nat, timestamp: bits, uniqueSig: nat)
      modifies this
      requires timestamp == time % T
      requires parameterConstraints ()
      requires stateInvariant (time, timestamp)
      ensures forwarded
      ensures stateInvariant (time, timestamp)
      ensures unchanged(this`queue) ensures unchanged(this`lastTime)
   {
      var tmpFiltering : bool := Get (filtering, nocalc, true);
      if tmpFiltering {
         bloomFilterInsert (uniqueSig);
         requestSet := requestSet + { uniqueSig };          // ghost update
      }
      generatePort(1, ProcessPacket(true, uniqueSig)); // CHANGE
      // forwarded := true;
   }

   function interval (timestamp: bits): bits
      reads this
      requires parameterConstraints ()
   {  timestamp / I } // implemented with a right-shift 
 
   function upperBoundedIncr (count: counter, unused: counter) : counter
   // this is a custom memcalc
   {  if count < U then (count + 1) else (count)  }

   function newTime (memVal: bits, timestamp: bits): bits
   // this is a custom memcalc
   {  if (timestamp - memVal) % T >= Q then (timestamp - Q) % T
      else memVal
   }

   ghost function creditedProtectingTime (time: nat) : int
      reads this
   {  time - (timeOn + Q)  }

   method processReply (ghost time: nat, timestamp: bits, uniqueSig: nat) 
                                                returns (recirc: RecircCmd)
      modifies this
      requires forwarded == false // CHANGE
      requires timestamp == time % T
      // There must be a packet between any two interval rollovers, so
      // that interval boundaries can be detected.  Unfortunately, the
      // specification is not strong enough to cause verification to fail
      // without this operating assumption.
         requires time - lastTime < T - I
      // Operating assumption to make attack time spans measurable.
         requires filtering.val ==> time < actualTimeOn + T
      requires parameterConstraints ()
      requires stateInvariant (time, timestamp)     
      // Adaptive Protection, requires exact request set
         ensures forwarded ==>                 
            (  ! protecting (time) || uniqueSig in preRequestSet )
      ensures ! forwarded ==>                               // Harmlessness
              (  protecting (time) && ! (uniqueSig in preRequestSet) ) 
      ensures stateInvariant (time, timestamp)
      ensures unchanged(this`queue) ensures unchanged(this`lastTime)
   {
      preRequestSet := requestSet;                          // ghost update
   // Changes to measurement state:
   // If an interval boundary has been crossed, save the count in
   // oldCount, and reset the counter to 1 (for this reply).  Otherwise
   // simply increment the count.
   // If there is an interval with no reply packets, then the count
   // will not be reset for that interval.  However, the count will
   // never include replies from more than one interval.
      var oldCount : counter := 0;                               
      var tmpCurrentIntv : bits;
      var tmpCount : counter;
      tmpCurrentIntv, currentIntv := GetSet (
         currentIntv, nocalc, 0, swapcalc, interval (timestamp) );
      if interval (timestamp) != tmpCurrentIntv {
         oldCount, count := GetSet ( count, nocalc, 0, swapcalc, 1 );
         tmpCount := 1;
      }
      else {
         tmpCount, count := GetSet (count, upperBoundedIncr, 0,
                                           upperBoundedIncr, 0);
      }
      assert count.val > 0;                                          
      assert (oldCount > 0) ==> (currentIntv.val != tmpCurrentIntv);

   // Changes to filtering state:
   // Turning filtering on:
   // Filtering is turned on as soon as count reaches upper threshold.
   // (Note that in !filtering test of count, it should never exceed U, so
   // this is defensive programming.)
      var tmpFiltering : bool := Get (filtering, nocalc, true);
      var tmpTimestampOn : bits;
      if ! tmpFiltering {
         tmpTimestampOn := Get (timestampOn, nocalc, 0);
         if tmpCount >= U { // time to turn filtering on
            var tmpRecircPending : bool;
            tmpRecircPending, recircPending := GetSet (
               recircPending, nocalc, true, swapcalc, true);
            if ! tmpRecircPending {
               recirc := RecircCmd (true, SetFiltering(true));
            }
            // else recirc already generated, do nothing
            else {  recirc := RecircCmd (false, Non());  }
         }
         else {  recirc := RecircCmd (false, Non());  }
         assert count.val >= U ==>        // Attack Response (partial spec)
                (  recircPending.val 
                || recirc == RecircCmd (true, SetFiltering(true))  );
         assert count.val < U ==> recirc == RecircCmd (false, Non());
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
            if oldCount >= L {
               ghost var oldTimestampOn := timestampOn.val;        // ghost
               tmpTimestampOn, timestampOn := GetSet (
                  timestampOn, newTime, timestamp, newTime, timestamp);
               if oldTimestampOn != tmpTimestampOn { 
                  timeOn := time - Q;                       // ghost update
               }
               recirc := RecircCmd (false, Non());
            }
            else { // oldCount < L
               tmpTimestampOn := Get (timestampOn, nocalc, 0);
               if (timestamp - tmpTimestampOn) % T >= Q + Roff {
                  // time to turn filtering off
                  var tmpRecircPending : bool;
                  tmpRecircPending, recircPending := GetSet (
                     recircPending, nocalc, true, swapcalc, true);
                  if ! tmpRecircPending {
                     recirc := RecircCmd (true, SetFiltering(false));
                  }
                  // else recirc already generated, do nothing
                  else {  recirc := RecircCmd (false, Non());  }
               }
            // count is low, just waiting for QRoff to elapse
            recirc := RecircCmd (false, Non());
            }
            assert                               // Modified Letup Response
            creditedProtectingTime (time) >= Roff as int ==> 
                (  recircPending.val 
                || recirc == RecircCmd (true, SetFiltering(true))  );
         }  // end of case where interval boundary crossed
         else {  tmpTimestampOn := Get (timestampOn, nocalc, 0);
                 recirc := RecircCmd (false, Non());           }
      }  // end of filtering case

   // Filtering decision:
      if tmpFiltering && (timestamp - tmpTimestampOn) % T >= Q {
         filter (time, timestamp, uniqueSig);
      }
      else {  generatePort(1, ProcessPacket(false, uniqueSig));  }// CHANGE
      // else {  forwarded := true; }
   }

   method filter (ghost time: nat, timestamp: bits, uniqueSig: nat) 
      modifies this
      requires forwarded == false // CHANGE
      requires timestamp == time % T
      requires protectImplmnt (timestamp) 
      requires preRequestSet == requestSet
      requires parameterConstraints ()
      requires stateInvariant (time, timestamp)
      ensures forwarded ==>  // Adaptive Protection, needs exact requestSet
                             uniqueSig in preRequestSet
      ensures ! forwarded ==> !(uniqueSig in preRequestSet) // Harmlessness
      ensures protecting (time)
      ensures stateInvariant (time, timestamp)
      ensures unchanged(this`queue) ensures unchanged(this`lastTime)
   {
      var do_forward := bloomFilterQuery (uniqueSig); // CHANGE
      if do_forward {                 // if positive is false, has no effect
         generatePort(1, ProcessPacket(false, uniqueSig)); // CHANGE
         requestSet := requestSet - { uniqueSig };          // ghost update
      }
   }

   method setFiltering (ghost time: nat, timestamp: bits, toWhat: bool) 
      modifies this
      requires timestamp == time % T
      requires parameterConstraints ()
      requires stateInvariant (time, timestamp)
      ensures unchanged(this`queue) ensures unchanged(this`lastTime)
      ensures stateInvariant (time, timestamp)
   {
      filtering := Set (filtering, swapcalc, toWhat);
      if toWhat {
         timestampOn := Set (timestampOn, swapcalc, timestamp);
         timeOn := time;                                    // ghost update
         actualTimeOn := time;                              // ghost update
      }
      else {  requestSet := {}; }                           // ghost update
      recircPending := Set (recircPending, swapcalc, false);
   }

   method simulatedHardwareFailure (ghost time: nat, timestamp: bits)    // ghost
      modifies this
      requires timestamp == time % T
      requires parameterConstraints ()
      requires stateInvariant (time, timestamp)
      ensures unchanged(this`queue) ensures unchanged(this`lastTime)
      ensures stateInvariant (time, timestamp)
   {
      filtering, recircPending := Atomic (false), Atomic (false);
      timeOn, actualTimeOn := 0, 0;
      currentIntv, timestampOn, count := Atomic(0), Atomic(0), Atomic(0);
      requestSet := {};
   }

   method simulatedClockTick (ghost time: nat, timestamp: bits)          // ghost
      modifies this
      requires timestamp == time % T
      requires parameterConstraints ()
      requires stateInvariant (time, timestamp)
      // Operating assumption to make attack time spans measurable.  
      // Without the "+ 1", the method cannot be verified.
         requires filtering.val ==> (time + 1) < actualTimeOn + T
      ensures unchanged(this`queue) ensures unchanged(this`lastTime)
      ensures stateInvariant (time, timestamp)
   {
      var timePlus : nat := time + 1;
      var timestampPlus : bits := (timestamp + 1) % T;
      assert stateInvariant (timePlus, timestampPlus);
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
      ensures uniqueSig in requestSet ==> inSet
   // No false positives:
   // Not true, but used to prove Adaptive Protection as a sanity
   // check.  (If deleted, Adaptive Protection cannot be proved.)  This
   // property can be false for two reasons: (1) it is the nature of
   // a Bloom filter to yield false positives sometimes; (2) in a
   // sliding-window Bloom filter, there are no timely deletions, just
   // scheduled timeouts which can be delayed.
      ensures ! (uniqueSig in requestSet) ==> (! inSet)
}
}
