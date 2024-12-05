abstract module LucidBase {

   type Event (==)

   type bits = x : int | 0 <= x < 256      // number must match parameter T

   datatype TimedEvent = 
      TimedEvent (event: Event, ghost time: nat, timestamp: bits)

   datatype RecircCmd = RecircCmd (generate: bool, event: Event)

   class Program {
      const T : nat := 256               // number must match limit on bits
      var queue : seq <TimedEvent>
      ghost var lastTime : nat

      ghost predicate parameterConstraints ()  // may be defined in program
         reads this

      ghost predicate arraySizes ()          // must be defined in program;
         reads this                          // if the program does not use
                                             // arrays, define as true

      ghost predicate stateInvariant (time: nat, timestamp: bits) // define
         reads this                                           // in program
         requires arraySizes ()
         requires timestamp == time % T
         ensures arraySizes ()
         ensures timestamp == time % T

      ghost predicate validQueue (q: seq <TimedEvent>)   // queue invariant
      // In a valid queue, times and timestamps match, and time is 
      // nondecreasing.
      {   
         match |q| {
            case 0 => true
            case _ =>  
               (  forall j | 0 <= j < |q| :: 
                     q[j].timestamp == q[j].time % T  )
            && (  forall j | 0 <= j < |q|-1 :: 
                     q[j].time <= q[j+1].time         )
      }  }
      
      ghost predicate operatingAssumptions (e: TimedEvent)        // may be
         reads this                                   // defined in program
         requires arraySizes ()
         requires e.timestamp == e.time % T
         requires stateInvariant (e.time, e.timestamp)
         ensures arraySizes ()

      constructor ()                          // must be defined in program
         ensures validQueue (queue)
         ensures parameterConstraints ()
         ensures arraySizes ()
         ensures stateInvariant (0, 0)

      method {:axiom} {:extern}  simulateArrival ()
         modifies this`queue
         requires validQueue (queue)
         ensures validQueue (queue)
         ensures |queue| == |old(queue)| + 1
         ensures queue[0..|old(queue)|] == old(queue)

      method  pickNextEvent (q: seq <TimedEvent>)
         modifies this
         requires |queue| > 0
         requires q == queue
         requires validQueue (q)
         requires parameterConstraints ()
         requires arraySizes ()
         requires stateInvariant (q[0].time, q[0].timestamp)
         // If the head of the queue does not satisfy the operating
         // assumptions, then this execution is permanently blocked (but
         // other valid executions will proceed).
            requires operatingAssumptions (q[0])
         ensures validQueue (queue)
      {  
         var recirc := dispatch(q[0]);
         if recirc.generate { generateRecircEvent (recirc.event); }
         this.queue := q[1..];
         lastTime := q[0].time;
      }

      method  dispatch (e: TimedEvent) returns (recirc: RecircCmd)
         modifies this                        // must be defined in program
         requires e.timestamp == e.time % T
         requires |queue| > 0
         requires arraySizes ()
         requires stateInvariant (e.time, e.timestamp)
         requires operatingAssumptions (e)
         requires validQueue(queue)
         requires parameterConstraints ()
         ensures unchanged(this`queue) ensures unchanged(this`lastTime)
         ensures validQueue (queue)
         ensures arraySizes ()
         ensures stateInvariant (e.time, e.timestamp)

      method  generateRecircEvent (e: Event)
         modifies this`queue
         requires validQueue (queue)
         requires |queue| > 0              // because method is called just
                    // after dispatch, when dispatched event still in queue
         ensures validQueue (queue)
      {
         var recircEvent: TimedEvent;
         var recircTimestamp: bits;
         if |queue[1..]| == 0 {
            recircTimestamp := (queue[0].timestamp + 1) % T;
            recircEvent := 
               TimedEvent (e, queue[0].time + 1, recircTimestamp);
         } 
         else {
            recircTimestamp := (queue[|queue|-1].timestamp + 1) % T;
            recircEvent := 
               TimedEvent (e, queue[|queue|-1].time + 1, recircTimestamp);
         }
         queue := queue + [recircEvent];
      }
   }
}

module  StateMemops {
   type  memcalc<!t> = (t, t) -> t

   datatype  StateVar<t> = Atomic (val: t)

   method  Get<t> (s:StateVar<t>, mget: memcalc, garg: t) returns (oldVal:t)
   ensures oldVal == mget(s.val, garg)
   {  
      oldVal := mget (s.val, garg);
   }

   method  Set<t> (s: StateVar<t>, mset: memcalc, sarg: t)
                                              returns (newVal: StateVar<t>)
   ensures newVal.val == mset(s.val, sarg)
   {  
      newVal := Atomic (mset (s.val, sarg));
      // must be called so that s := newVal;
   }

   method  GetSet<t> (s: StateVar<t>, mget: memcalc, garg: t,
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

module ArrayMemops {


   type  bits = x : int | 0 <= x < 256      // number must match parameter T


   type  tout<t> = t



   type {:extern "MCTY"} memcalc<!t> = (t, t) -> tout<t>

   

   datatype {:extern}  ArrayVar<t> = Atomic (cells: seq<t>)

   function  Create<t> (n: nat, init: t) : ArrayVar<t>
   {
      Atomic (seq(n, (_ => init)))
   }

   method  {:extern} Get<t> (s: ArrayVar<t>, idx: bits, mget: memcalc, garg: t) 
                                                        returns (oldVal: t)
   requires 0 <= idx < |s.cells|
   ensures oldVal == mget(s.cells[idx], garg)
   {
      oldVal := mget (s.cells[idx], garg);
   }

   method  {:extern} Set<t> (s: ArrayVar<t>, idx:bits, mset: memcalc, sarg: t)
                                            returns (newArray: ArrayVar<t>)
   requires 0 <= idx < |s.cells|
   ensures |newArray.cells| == |s.cells|
   // The following line says that newArray is the same as s, except that
   // newArray.cells[idx] is updated to be mset(s.cells[idx], sarg).
   ensures newArray.cells == s.cells[idx := mset(s.cells[idx], sarg)]
   {
      newArray := Atomic (s.cells[idx := mset(s.cells[idx], sarg)]);
      // must be called so that s := newVal;
   }

   method  {:extern} GetSet<t> (s: ArrayVar<t>, idx: bits, mget: memcalc, garg: t,
                                                mset: memcalc, sarg: t)
                                 returns (oldVal: t, newArray: ArrayVar<t>)
   requires 0 <= idx < |s.cells|
   ensures oldVal == mget(s.cells[idx], garg)
   ensures |newArray.cells| == |s.cells|
   ensures newArray.cells == s.cells[idx := mset(s.cells[idx], sarg)]
   {
      oldVal := mget (s.cells[idx], garg);
      newArray := Atomic (s.cells[idx := mset(s.cells[idx], sarg)]);
      // must be called so that s := newVal;
   }

   // generic memcalcs
   function  nocalc<t> (oldVal: t, newArg: t) : t {  oldVal  }
   function  swapcalc<t> (oldVal: t, newArg: t) : t {  newArg  }


}
