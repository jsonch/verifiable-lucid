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
        modifies this`recircQueue, this`trace, this`emittedEvents
        requires arrived(a(x))
        ensures  finished(a(x))       
        ensures  generated(b(x))      
        ensures  emitted(1, a(x))
    {
        generate(b(x));
        generate_port(1, a(x));
        finish(a(x));
    }

    method B(y : uint32)
        modifies this`recircQueue, this`trace
        requires arrived(b(y))
        ensures  finished(b(y))
    {
        finish(b(y));        
    }    
}

// Outside of the program, prove some properties about the trace. 
// For example, you can't process two events on the same cycle.
method traceTest() 
    {
        var nextEvent;
        var p := new Program();
        p.A(1); // A is the handler method, calling it directly models the event arriving and being handled immediately.
        p.clockTick(); // manually tick the clock -- give user absolute control over inter-arrival properties
        p.clockTick();
        p.A(1);
        assert |p.recircQueue| == 2; // Each A generates a recirculated event, so the queue has 2 events in it
        p.clockTick();

        nextEvent := p.getNextRecirc(); // Get an event out of the recirculation queue and process it.
        match nextEvent {case b(x) => p.B(x);} // the verifier knows that the event is a b!
        p.clockTick();
        nextEvent := p.getNextRecirc();
        match nextEvent {case b(x) => p.B(x);}

        // reason about output
        assert p.emittedEvents[(1, 0)] == a(1);
        assert p.emittedEvents[(1, 0)] == a(1);


        // reason about execution trace
        assert p.trace[0] == a(1);
        assert 1 !in p.trace;
        assert p.trace[2] == a(1);
        assert p.trace[3] == b(1);
        assert p.trace[4] == b(1);
    }

}
