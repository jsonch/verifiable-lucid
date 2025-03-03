// A simple program to illustrate reasoning about properties of a 
// trace and program IO

include "verifiableLucid.dfy"

module LucidProg refines VerifiableLucid {

// declare some events
datatype Event = 
    | a(x : uint32)
    | b(y : uint32)

// declare the "Program", with the handlers and the state
class Program ... {

    method A(x : uint32) 
        modifies this`generatedEvent
        modifies this`emittedEvents
        modifies this`trace
        requires readyToHandle(a(x))
        ensures  generates(b(x))  // generates a recirculation event
        ensures  emits(1, a(x))   // forwards an event to a port (port 1)
        ensures  records(a(x))    // less important: we log the processing of this event
    {
        generate(b(x));
        generate_port(1, a(x)); 
        record(a(x));
    }

    method B(y : uint32)
        modifies this`trace
        requires readyToHandle(b(y))
        ensures  records(b(y))
    {
        record(b(y));
    }    
}


// note/idea: enforce higher input priority for recirculation events
// Outside of the program, prove some properties about the trace. 
// For example, you can't process two events on the same cycle.
method traceTest()
    {
        var p := new Program();
        p.clockTick();      // increment system time by 1.
        assert |p.recircQueue| == 0;
        p.A(1);             // Calling a handler represents an event arriving from the network.
        p.clockTick();
        assert |p.recircQueue| == 1;
        p.clockTick();
        p.A(1);
        p.clockTick();
        assert |p.recircQueue| == 2;
        var nextEvent := p.nextRecirc();
        match nextEvent {case b(x) => p.B(x);} // the verifier knows that the event is a b!
        p.clockTick();
        assert |p.recircQueue| == 1;

        assert p.recircQueue[0].1 == b(1);

        // reason about execution trace
        assert p.trace[1] == a(1);
        assert 0 !in p.trace;
        assert p.trace[3] == a(1);
        assert p.trace[4] == b(1);
    }

}
