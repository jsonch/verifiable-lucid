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
-------------------------------------------------------------------------*/


abstract module LucidBase {

   type uint8 = x : nat | 0 <= x < 256
   type uint16 = x : nat | 0 <= x < 65536
   type uint20 = x : nat | 0 <= x < 1048576
   type uint24 = x : nat | 0 <= x < 16777216
   type uint32 = x : nat | 0 <= x < 4294967296

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

   class Program {
      var sys : Sys

      var generatedEvents : set<GeneratedEvent>  // the event generated for recirc

      ghost predicate parameterConstraints ()          // define in program
         reads {this} - {sys}
      ghost predicate stateInvariant (time: nat, timestamp: uint8, lastTime:nat)
         reads {this} - {sys}                                    // define in program

      ghost predicate operatingAssumptions (event: Event, time : nat, timestamp: uint8, lastTime:nat)     
         reads {this} - {sys}                                        // define in program


      constructor ()                                   // define in program
         ensures sys.validQueue (sys.queue)
         // ensures parameterConstraints () // problem: how can the constructor ever ensure this?
         ensures fresh(sys)
         ensures fresh(this)
         {
            sys := new Sys();
         }

      // method simulateArrival (q: seq <TimedEvent>)
      // // This method adds zero or more events to the queue.
      //    modifies this
      //    requires validQueue (queue)
      //    requires q == queue
      //    ensures q <= queue           // old queue is a prefix of new queue
      //    ensures validQueue (queue)

      method pickNextEvent (q: seq <TimedEvent>)
         modifies this, this.sys, sys`lastTime
         requires generatedEvents == {}
         requires sys.validQueue (sys.queue)
         requires |sys.queue| > 0
         requires q == sys.queue
         requires parameterConstraints ()
         requires stateInvariant (q[0].time, q[0].timestamp, sys.lastTime)
         requires (sys.time == q[0].time && sys.timestamp == q[0].timestamp) <==> stateInvariant (q[0].time , q[0].timestamp, sys.lastTime)
         requires operatingAssumptions (q[0].event, q[0].time, q[0].timestamp, sys.lastTime)
         ensures sys.validQueue (sys.queue)
         ensures ( |sys.queue| == |q| - 1 ) || ( |sys.queue| == |q| )
      { 
         assert stateInvariant (q[0].time, q[0].timestamp, sys.lastTime);
         sys.time := q[0].time;
         sys.timestamp := q[0].timestamp;
         assert stateInvariant (sys.time, q[0].timestamp, sys.lastTime);

         // sys.timestamp := q[0].timestamp;         
         dispatch(q[0].event);
         sys.lastTime := 0;
         // if an event for recirculation was generated, add it to the queue
         sys.queue := q;
         assert |sys.queue| > 0;
         while |generatedEvents| > 0
            modifies this`generatedEvents
            modifies sys`queue
            invariant |sys.queue| > 0
            invariant sys.validQueue(sys.queue)
         {
            assert |sys.queue| > 0;
            var generatedEvent :| generatedEvent in generatedEvents;
            if (generatedEvent.ports == {}) { // recirc event, add to queue
               var recircEvent: TimedEvent := generateRecircEvent(generatedEvent.event);
               sys.queue := sys.queue + [recircEvent];
            }
            generatedEvents := generatedEvents - {generatedEvent};
         }
         sys.queue := q[1..];
         // lastTime := q[0].time; 
         sys.lastTime := q[0].time;
      }

      method dispatch (e: Event)
         modifies {this} - {this.sys}                                // define in program
         requires sys.timestamp == sys.time % sys.T
         requires parameterConstraints ()
         requires stateInvariant (sys.time, sys.timestamp, sys.lastTime)
         requires operatingAssumptions (e, sys.time, sys.timestamp, sys.lastTime)
         requires generatedEvents == {}
         ensures unchanged(this`sys)

      method generate(e : Event)            // generate recirculation event
         modifies this`generatedEvents
         ensures unchanged(this`sys)
      {
         generatedEvents := generatedEvents + {Event(e, {})};
      }
      method generate_port(p : uint8, e : Event)  // generate output event
         modifies this`generatedEvents
         ensures unchanged(this.sys)

      {
         generatedEvents := generatedEvents + {Event(e, {p})};
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
