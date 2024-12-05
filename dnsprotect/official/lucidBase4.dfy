/*-------------------------------------------------------------------------
VERIFIABLE LUCID SIMULATION MODULE FOR REFERENCE IMPLEMENTATIONS WITH
REFINEMENT OF UNBOUNDED NUMBERS AND
REFINEMENT OF EXTERNAL DATA STRUCTURES AND
REFINEMENT OF MEMORY ACCESSES
-------------------------------------------------------------------------*/

abstract module LucidBase {

   type bits = x : nat | 0 <= x < 256      // number must match parameter T

   type Event (==)
   datatype TimedEvent = 
      TimedEvent (event: Event, time: nat, timestamp: bits)
            
   datatype RecircCmd = RecircCmd (generate: bool, event: Event)

   class Program {
      const T : nat := 256               // number must match limit on bits
      var queue : seq <TimedEvent>
      var lastTime : nat

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
         ensures parameterConstraints ()
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
         recircTimestamp := (queue[|queue|-1].time + 1) % T;
         recircEvent := 
                   TimedEvent(e, queue[|queue|-1].time+1, recircTimestamp);
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
