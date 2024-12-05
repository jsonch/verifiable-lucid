/*-------------------------------------------------------------------------
SINGLE-SWITCH ALGORITHM AND ITS SPECIFICATION (verified)

This version adds to the third version the option for state variables to
be arrays.  This capability is designed for the following use case:
 * Each flow is identified by an address.
 * State variables are arrays because there is a different array element
   for each flow.
If it is necessary to use arrays for some other reason, it should be fairly
obvious how to adapt our code.

1) If a state variable is an array, it is now declared like this:
      var filtering : ArrayVar <bool> 
If a ghost variable is an array, it is now declared like this:
      ghost var timeOn : seq <nat> 
As you can see, an array ghost variable becomes a sequence.  The sequences
are a little easier to code with.  Sequences cannot be used for real state
variables, however, because of the need to package accesses to them as
memops.

2) There is a parameter A, which is the number of flows/addresses handled
by the program.  It is essential to define an arraySizes predicate, like
this:
   ghost predicate arraySizes ()
      {  
         |filtering.cells| == A                       // size of an array
      && |timeOn| == A                                // size of a sequence
      }
The arraySizes predicate appears so frequently in the code that it is not
optional.  If the program does not use arrays, then the predicate must
still be defined.  Simply define it as "true". 

3) Array variables are initialized as follows:
   constructor ()
   {
      filtering := Create (A, false);
      timeOn := seq (A, _ => 0);
   }

4) All events and state-accessing functions are modified to take an
additional argument, "addr : bits", which specifies the array index to be 
used.  The memops on array variables look and act just like the scalar 
memops, except for the extra "addr" argument.

5) The stateInvariant predicate is modified to describe the contents
of every cell in each array. i.e., there are now "forall" quantifiers in 
front of every part of the predicate.

6) Use our code as a model for specifying and implementing with array
state variables and ghost variables.  Note that, in specifications, 
requires/ensures arraySizes () must precede any other requires/ensures
clauses that reference arrays!

NOTE: Over time, the purpose of the rules below has become somewhat
blurred.  In the final version, we expect to have two clearly delineated
sets of rules: (i) rules implemented by a translator that converts a
properly formed "Ludafny" program to an equivalent Lucid program, (ii) 
programming rules that users should follow to refine a verified Dafny
program into a properly formed "Ludafny" program, verified according to an
equivalent specification.

Cumulative rules for translation to Lucid:
1) Drop the declaration of any variable declared "ghost."
2) Drop any statement updating a ghost variable (labeled by comment).
3) Drop any method, predicate or function declared ghost or labeled ghost
   (by comment).
4) Fill in the bodies of extern methods with executable and correct code.  5) Translate the "dispatch" method into the Lucid equivalent.  
In the following steps, refer to the two Memop modules in lucidBase4.dfy.
6) Declare all non-ghost state variables as StateVar or ArrayVar data 
   types.  Initialize their values with the Atomic or Create constructor.
7) Whenever a state variable is referred to in specifications or ghost 
   code, refer to it as "variable.val" or "variable.cells".
8) Whenever a state variable is read or written in executable code, it must
   be accessed through one of the three Memop methods Get, Set, or GetSet.
   Get and GetSet require temporary variables for returning the old (but
   possibly modified by the memcalc) value.
9) After adding the Memop methods, on every execution path, each state
   variable must be the subject of at most one Memop method.  The order of
   these Memop methods must be consistent with a particular total ordering
   of the state variables.
10)If (9) cannot be obeyed, then the second access to a state variable,
   for processing the same packet, must become the first access to the
   state variable in processing a recirculation packet (see next).
11)Every dispatched event returns a recirculation command.  If the event
   needs no recirculation packet, return:
      recirc := RecircCmd (false, Non());
   If the event needs a recirculation packet, return:
      recirc := RecircCmd (true, OtherEvent (arg)); 
   Then the Lucid base will generate a timed OtherEvent and add it to the
   queue.
-------------------------------------------------------------------------*/

/*-------------------------------------------------------------------------

Changes for Lucid translation: 

The dafny-to-lucid translator is implemented as a dafny backend, 
in an experimental dafny-compiler extension that lets you write 
transformation passes in dafny itself. The "dafny generated dafny" 
extension has some features that it does not support, so we have to make 
some changes to the program to use it. 

1. In LucidBase, make ArrayMemops and its helpers extern functions. 
   This should not change verification, but tells the compiler to skip 
   the bodies of the methods like Set, Get, etc. We have to do this because 
   dafny generated dafny doesn't support array update expressions, i.e., 
      s.cells[idx := mset(s.cells[idx], sarg)]
   This should not change the source-side verification.

2. The dafny compiler does not like that simulateArrival has no body, 
   so we just make it extern. 



-------------------------------------------------------------------------*/

include "lucidBase5.dfy"

module LucidProg refines LucidBase {
   import opened ArrayMemops

   type counter = x : nat | x < 1048576              // limit must exceed U

   datatype Event =
    | ProcessPacket (addr: bits, dnsRequest: bool, uniqueSig: bits)
    | SetFiltering (addr: bits, toWhat: bool)
    | SimulatedClockTick ()
    | SimulatedHardwareFailure ()
    | Non ()

class Program ... {

   // Parameters
   const I : nat := 16             // interval length, < T and a power of 2
   const Q : bits                              // maximum DNS response time
   const QRoff : bits   // Q plus observation window for stopping filtering
   ghost const W : nat                   // Bloom-filter window size, >= Q as nat
   const U : counter                               // upper count threshold
   const L : counter                               // lower count threshold
   const A : nat := 256      // array length, must equal range of bits type

   // Address State
   var currentIntv : ArrayVar <bits>              // current interval
   var count : ArrayVar <counter>          // counter for DNS replies
   var filtering : ArrayVar <bool>   // turns adaptive filtering on and off
   ghost var timeOn : seq <nat>   // effective time filtering was turned on
   var timestampOn : ArrayVar <bits>            // implementation of timeOn
   ghost var actualTimeOn : seq <nat>    // actual time filtering turned on
   var recircPending : ArrayVar <bool>   // a "semaphore" for recirculation
   ghost var forwarded: bool            // used to specify filtering result
   ghost var requestSet : seq <set <nat>>// pending requests, for filtering
   ghost var preFilterSet : seq <set <nat>>  // requestSet, before deletion


   // If no arrays are used, this predicate must be defined as "true".
   ghost predicate arraySizes ()
      {  |currentIntv.cells| == A
      && |count.cells| == A
      && |filtering.cells| == A
      && |timeOn| == A
      && |timestampOn.cells| == A
      && |actualTimeOn| == A
      && |recircPending.cells| == A
      && |requestSet| == A
      && |preFilterSet| == A
      }

   ghost predicate parameterConstraints ()           // from problem domain
      {  I > 0 && QRoff > Q > 0 && W >= Q && 0 < U < 1048576  }

   constructor ()
   {
      filtering, recircPending := Create (A, false), Create (A, false);
      timeOn, actualTimeOn := seq (A, _ => 0), seq (A, _ => 0);
      currentIntv, timestampOn, count:=Create(A,0),Create(A,0),Create(A,0);
      requestSet, preFilterSet := seq (A, _ => {}), seq (A, _ => {});
      requestSet := seq (1, _ => {});


   }

   ghost predicate protecting (addr : bits, time: nat) 
      reads this
      requires arraySizes ()
   {  filtering.cells [addr] && (time - actualTimeOn [addr]) >= Q as nat  }

   ghost predicate protectImplmnt (addr: bits, timestamp: bits) 
   // memops caused refactoring, which replaced this predicate
      reads this
      requires arraySizes ()
   {     filtering.cells [addr] 
      && elapsedTime (timestamp, timestampOn.cells [addr]) >= Q  }

   ghost function elapsedTime (now: bits, origin: bits): (res: bits)
      reads this
      // Function satisfies specification because of mod arithmetic.
         ensures now >= origin ==> res == (now - origin)
         ensures now < origin ==>                         // 0 is T as bits
            res == (now + T - origin)
   {  (now - origin) % T  }        // implemented as bit-vector subtraction

   ghost predicate stateInvariant (time: nat, timestamp: bits)
   {  (forall i :: 0 <= i < A ==> timestampOn.cells [i] == timeOn [i] % T)
   && (forall i :: 0 <= i < A ==> actualTimeOn [i] <= timeOn [i])
   && (forall i :: 0 <= i < A ==> timeOn [i] <= time)
   && (forall i :: 0 <= i < A ==> 
         (timeOn[i] > actualTimeOn[i]) ==> (time >= timeOn[i] + Q as nat))
   && (forall i :: 0 <= i < A ==>
         (filtering.cells [i] ==>
               (protecting (i, time) <==> protectImplmnt (i, timestamp))))
   && (forall i :: 0 <= i < A ==> 
         ! filtering.cells [i] ==> requestSet [i] == {})
   }

   ghost predicate operatingAssumptions (e: TimedEvent) 
   // There cannot be restrictions on recirculation events, i.e.,
   // SetFiltering events, because they were already chosen by the program.
   {
      if   e.event.ProcessPacket?
      then (  (filtering.cells [e.event.addr] ==> 
                 e.time < actualTimeOn [e.event.addr] + T) 
           && (e.time - lastTime < T - I)                )
      else if e.event.SimulatedClockTick?
      then (forall i :: 0 <= i < A ==>
              filtering.cells [i] ==> (e.time + 1) < actualTimeOn [i] + T) 
      else true
   }

   method dispatch (e: TimedEvent) returns (recirc: RecircCmd)
   {  
      // enforced dispatch / handler form: 
      // 1. the handler function h for event e takes 
      //    e's arguments followed by an optional timestamp argument. 
      //    when called, the timestamp argument must always be 
      //    e's timestamp.
      // 2. the handler function h has the same name as e, 
      //    but with a lowercase first letter.
      // 3. h always returns a RecircCommand
      // If we assume this convention, we can ignore the 
      // dispatch method entirely in translation. 
      recirc := RecircCmd (false, Non());
      if {
         case e.event.ProcessPacket? => 
         {  recirc := processPacket (e.event.addr,  
               e.event.dnsRequest, e.event.uniqueSig,
               e.time, e.timestamp);
         }
         case e.event.SetFiltering? => 
            setFiltering (e.event.addr,e.event.toWhat,e.time,e.timestamp);
         case e.event.SimulatedClockTick? => 
            simulatedClockTick (e.time, e.timestamp);
         case e.event.SimulatedHardwareFailure? => 
            simulatedHardwareFailure (e.time, e.timestamp);
         case e.event.Non? => 
      }
   } 



   function interval (timestamp: bits): bits
      reads this
      requires parameterConstraints ()
   {  timestamp / I  }                    // implemented with a right-shift
 
   function upperBoundedIncr (count: counter, unused: counter) : counter
   {
      
         if count < U then (count + 1) else (count)  
   }

   function newTime (memVal: bits, timestamp: bits): bits
   // this is a custom memcalc
   ensures true
   {  if (timestamp - memVal) % T >= Q then (timestamp - Q) % T
      else memVal

   }

   method {:extern} {:axiom} bloomFilterInsert (addr: bits, uniqueSig: bits)

   method {:extern} {:axiom} bloomFilterQuery (addr: bits, uniqueSig: bits) 
                                                      returns (inSet: bool)
      requires arraySizes ()
      ensures arraySizes ()
   // No false negatives:
   // A sliding-window Bloom filter automatically deletes set members
   // shortly after a guaranteed tenancy W.  You might imagine that
   // this would be a source of false negatives.  However, it is not,
   // because a request never needs to stay in the set longer than Q,
   // where Q <= W.
      ensures uniqueSig in requestSet [addr] ==> inSet
   // No false positives:
   // Not true, but used to prove Adaptive Protection as a sanity
   // check.  (If deleted, Adaptive Protection cannot be proved.)  This
   // property can be false for two reasons: (1) it is the nature of
   // a Bloom filter to yield false positives sometimes; (2) in a
   // sliding-window Bloom filter, there are no timely deletions, just
   // scheduled timeouts which can be delayed.
      ensures ! (uniqueSig in requestSet [addr]) ==> (! inSet)

   method filter (addr: bits, ghost time: nat, timestamp: bits, uniqueSig: bits) 
                                                  returns (ghost forwarded: bool)
      modifies this
      requires timestamp == time % T
      requires parameterConstraints ()
      requires arraySizes ()
      requires stateInvariant (time, timestamp)
      requires protectImplmnt (addr, timestamp)
      requires preFilterSet == requestSet
      ensures arraySizes ()
      ensures stateInvariant (time, timestamp)
      ensures     ! (uniqueSig in preFilterSet [addr])
              ==> ! forwarded                     // Adaptive Protection,
                                                  // needs exact requestSet
      ensures ! forwarded ==>                               // Harmlessness
                 ! (uniqueSig in preFilterSet [addr])
      ensures unchanged(this`queue) ensures unchanged(this`lastTime)
   {
      forwarded := bloomFilterQuery (addr, uniqueSig);
      if forwarded {                 // if positive is false, has no effect
         requestSet := requestSet [addr := requestSet[addr] - {uniqueSig}];
                                                            // ghost update
      }
   }


   method processRequest (addr : bits, ghost time: nat, timestamp: bits, 
                                  uniqueSig: bits) returns (ghost forwarded: bool)
      modifies this
      requires timestamp == time % T
      requires parameterConstraints ()
      requires arraySizes ()
      requires stateInvariant (time, timestamp)
      ensures forwarded
      ensures unchanged(this`queue) ensures unchanged(this`lastTime)
      ensures arraySizes ()
      ensures stateInvariant (time, timestamp)
   {
      var tmpFiltering : bool := Get (filtering, addr, nocalc, true);
      if (tmpFiltering) {
         bloomFilterInsert (addr, uniqueSig); 
         requestSet := requestSet[addr := requestSet[addr] + {uniqueSig}]; 
                                                            // ghost update
      }
      forwarded := true;                                    // ghost update
   }

   method processReply (addr:bits, ghost time:nat, timestamp:bits, uniqueSig:bits)
                               returns (ghost forwarded: bool, recirc: RecircCmd)
      modifies this
      requires timestamp == time % T
      // There must be a packet between any two interval rollovers, so
      // that interval boundaries can be detected.  Unfortunately, the
      // specification is not strong enough to cause verification to fail
      // without this operating assumption.
         requires time - lastTime < T - I
      requires parameterConstraints ()
      requires arraySizes ()
      requires stateInvariant (time, timestamp)
      requires preFilterSet == requestSet
      // Operating assumption to make attack time spans measurable.
         requires filtering.cells [addr] ==> time < actualTimeOn [addr] + T
      ensures unchanged(this`queue) ensures unchanged(this`lastTime)
      ensures arraySizes ()
      ensures stateInvariant (time, timestamp)
      ensures (protecting(addr,time) && !(uniqueSig in preFilterSet[addr]))
              ==> ! forwarded                     // Adaptive Protection,
                                                  // needs exact requestSet
      ensures ! forwarded ==>                               // Harmlessness
                 ! (uniqueSig in preFilterSet [addr] )
   {
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
         currentIntv, addr, nocalc, 0, swapcalc, interval (timestamp) );
      if interval (timestamp) != tmpCurrentIntv {
         oldCount, count := GetSet ( count, addr, nocalc, 0, swapcalc, 1 );
         tmpCount := 1;
      }
      else {
         tmpCount, count := GetSet (count, addr, upperBoundedIncr, 0,upperBoundedIncr, 0);
      }
      // tmpCount := count.cells [addr];  // inlined computation for tmpCount
      assert count.cells [addr] > 0;                                 // new
      assert (oldCount > 0) ==> 
         (currentIntv.cells [addr] != tmpCurrentIntv);               // new

   // Changes to filtering state:
   // Turning filtering on:
   // Filtering is turned on as soon as count reaches upper threshold.
   // (Note that in !filtering test of count, it should never exceed U, so
   // this is defensive programming.)
      var tmpFiltering : bool := Get (filtering, addr, nocalc, true);
      var tmpTimestampOn : bits;
      if ! tmpFiltering {
         if tmpCount >= U { // time to turn filtering on
            var tmpRecircPending : bool;
            tmpRecircPending, recircPending := GetSet (
               recircPending, addr, nocalc, true, swapcalc, true);
            if ! tmpRecircPending {
               recirc := RecircCmd (true, SetFiltering(addr, true));
            }
            // else recirc already generated, do nothing
            else {  recirc := RecircCmd (false, Non());  }
         }
         else {  recirc := RecircCmd (false, Non());  }
         assert tmpCount >= U ==> 
                (  recircPending.cells [addr]
                || recirc == 
                      RecircCmd (true, SetFiltering(addr,true))  );   //new
         assert tmpCount < U ==> recirc == RecircCmd (false, Non());  //new
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
               ghost var oldTimestampOn := timestampOn.cells [addr];//ghost
               tmpTimestampOn, timestampOn := GetSet (
                  timestampOn,addr,newTime,timestamp,newTime,timestamp);
               if oldTimestampOn != tmpTimestampOn {               // ghost
                  timeOn := timeOn [addr := time - Q];             // ghost
               }
               recirc := RecircCmd (false, Non());
            }
            else { // oldCount < L
               tmpTimestampOn := Get (timestampOn, addr, nocalc, 0);
               if (timestamp - tmpTimestampOn) % T >= QRoff {
                  // time to turn filtering off
                  var tmpRecircPending : bool;
                  tmpRecircPending, recircPending := GetSet (
                     recircPending, addr, nocalc, true, swapcalc, true);
                  if ! tmpRecircPending {
                     recirc := RecircCmd (true, SetFiltering(addr, false));
                  }
                  // else recirc already generated, do nothing
                  else {  recirc := RecircCmd (false, Non());  }
               }
            // count is low, just waiting for Woff to elapse
            recirc := RecircCmd (false, Non());
            }
         }  // end of case where interval boundary crossed
         else {  tmpTimestampOn := Get (timestampOn, addr, nocalc, 0);
                 recirc := RecircCmd (false, Non());                 }
         assert (! (elapsedTime (timestamp, timestampOn.cells[addr]) >= Q))
                ==> (  recircPending.cells [addr]
                    || recirc == RecircCmd (false, Non())  );        // new
         assert (  elapsedTime (timestamp, timestampOn.cells [addr]) >= Q
                && oldCount > 0
                && (  oldCount < L
                   && elapsedTime (timestamp, timestampOn.cells [addr]) 
                         >= QRoff                                     )  )
                ==> (  recircPending.cells [addr]  
                    || recirc == 
                       RecircCmd (true, SetFiltering (addr, false)));// new
         assert 
         (  elapsedTime (timestamp, timestampOn.cells [addr]) >= Q
         && (  (! (oldCount > 0))
            || (! (  oldCount < L                                    // new
                   && elapsedTime (timestamp, timestampOn.cells [addr]) 
                         >= QRoff                                     )  )
         )  )                                                            
         ==> (  recircPending.cells [addr]
             || recirc == RecircCmd (false, Non())  );               // new
      }  // end of filtering case

   // Filtering decision:
      if tmpFiltering && (timestamp - tmpTimestampOn) % T >= Q {
         forwarded := filter (addr, time, timestamp, uniqueSig);
      }
      else {  forwarded := true; }
   }


   method processPacket (addr: bits, dnsRequest: bool, uniqueSig: bits,
         ghost time: nat, timestamp: bits) returns (recirc: RecircCmd)
      modifies this
      requires timestamp == time % T
      // There must be a packet between any two interval rollovers, so
      // that interval boundaries can be detected.  Unfortunately, the
      // specification is not strong enough to cause verification to fail
      // without this operating assumption.
         requires time - lastTime < T - I
      requires parameterConstraints ()
      requires arraySizes ()
      requires stateInvariant (time, timestamp)
      // Below is the operating assumption to make attack time spans 
      // measurable.
         requires filtering.cells [addr] ==> time < actualTimeOn [addr] + T
      ensures arraySizes ()
      ensures stateInvariant (time, timestamp)
      ensures (  ! dnsRequest && protecting (addr, time)
              && ! (uniqueSig in preFilterSet [addr])   ) 
              ==> ! forwarded                     // Adaptive Protection,
                                                  // needs exact requestSet
      ensures ! forwarded ==>                               // Harmlessness
              (  ! dnsRequest && ! (uniqueSig in preFilterSet [addr])  )
      ensures unchanged(this`queue) ensures unchanged(this`lastTime)
   {
      if (dnsRequest) {  
         forwarded := processRequest (addr, time, timestamp, uniqueSig); 
                                                                   // ghost
         recirc := RecircCmd (false, Non());
      }
      else { 
         preFilterSet := requestSet;                        // ghost update
         forwarded, recirc := processReply (addr, time, timestamp, 
                                                                uniqueSig);
      }   
   }



   method setFiltering (addr: bits, toWhat: bool, ghost time:nat, timestamp:bits)
      modifies this
      requires timestamp == time % T
      requires parameterConstraints ()
      requires arraySizes ()
      requires stateInvariant (time, timestamp)
      ensures unchanged(this`queue) ensures unchanged(this`lastTime)
      ensures arraySizes ()
      ensures stateInvariant (time, timestamp)
   {
      filtering := Set (filtering, addr, swapcalc, toWhat);
      if toWhat {
         timestampOn := Set (timestampOn, addr, swapcalc, timestamp);
         timeOn := timeOn [addr := time];                   // ghost update
         actualTimeOn := actualTimeOn [addr := time];       // ghost update
      }
      else {  requestSet := requestSet [addr := {}]; }      // ghost update
      recircPending := Set (recircPending, addr, swapcalc, false);
   }

   method simulatedClockTick (ghost time: nat, timestamp: bits)          // ghost
      modifies this
      requires timestamp == time % T
      requires parameterConstraints ()
      requires arraySizes ()
      requires stateInvariant (time, timestamp)
      // Operating assumption to make attack time spans measurable.  
      // Without the "+ 1", the method cannot be verified.
         requires forall i :: 0 <= i < A ==> 
            filtering.cells [i] ==> (time + 1) < actualTimeOn [i] + T
      ensures unchanged(this`queue) ensures unchanged(this`lastTime)
      ensures arraySizes ()
      ensures stateInvariant (time, timestamp)
   {
      var timePlus : nat := time + 1;
      var timestampPlus : bits := (timestamp + 1) % T;
      assert stateInvariant (timePlus, timestampPlus);
   }

   method simulatedHardwareFailure (ghost time: nat, timestamp: bits)    // ghost
      modifies this
      requires timestamp == time % T
      requires parameterConstraints ()
      requires arraySizes ()
      requires stateInvariant (time, timestamp)
      ensures unchanged(this`queue) ensures unchanged(this`lastTime)
      ensures arraySizes ()
      ensures stateInvariant (time, timestamp)
   {
      filtering, recircPending := Create (A, false), Create (A, false);
      timeOn, actualTimeOn := seq (A, _ => 0), seq (A, _ => 0);
      currentIntv, timestampOn, count:=Create(A,0),Create(A,0),Create(A,0);
      requestSet, preFilterSet := seq (A, _ => {}), seq (A, _ => {});
   }

}
}
