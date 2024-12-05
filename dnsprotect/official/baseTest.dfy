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
}
