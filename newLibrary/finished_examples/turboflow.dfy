/*

This implements the data plane cache of TurboFlow. 

TurboFlow is a flow telemetry system with two components: 
    - a Data plane cache measures per-flow flow metrics (e.g., total packet count) 
      over short time intervals. When the cache evicts a flow, 
      it sends a record of its current aggregate metrics to a collection server.       
    - The collection server aggregates records from the cache to calculate 
      per-flow metrics for the entire duration of every flow. 

The main property of the data plane cache is: 
    For every flow that has been seen by the cache, 
    the counter in the cache + the sum of the counts sent to the server 
    = the true total count of the flow

Idea: 
Thinking about correctness, TurboFlow is susceptible to packet loss... 
Can we make a stronger implementation that is robust against it to some degree?
*/


include "verifiableLucid.dfy"

module BloomFilter refines VerifiableLucid {

    datatype Event = 
        | Packet(src : uint32, dst : uint32, len : uint32)
        | FlowRecord(src : uint32, dst : uint32, len : uint32)

    class Program ... {
        const nFlows : nat := 1024
        const seed : nat := 7
        const collectorPort : nat := 0

        var srcs : LArray<uint32>
        var dsts : LArray<uint32>
        var lens : LArray<uint32>

        ghost var ArrayRepr : set<object>
        ghost predicate ValidArrays()
            reads this, ArrayRepr
        {
            // Repr contents
                (ArrayRepr == {srcs, dsts, lens})
            // Non-aliasing
            && srcs != dsts && srcs != lens && dsts != lens
            // array lengths
            && |srcs.cells| == |dsts.cells| == |lens.cells| == 1024
        }

        constructor ()
        ensures ValidArrays()
        {
            srcs := new LArray<uint32>.Create(nFlows, 0);
            dsts := new LArray<uint32>.Create(nFlows, 0);
            lens := new LArray<uint32>.Create(nFlows, 0);
            ArrayRepr := {srcs, dsts, lens};
        }

        // memops
        function incr (oldVal: uint32, incrBy: uint32) : uint32 { 
            to_uint32(oldVal + incrBy) 
        }
        function memval (oldVal: uint32, unused: uint32) : uint32 { oldVal }
        function newval (oldVal: uint32, newVal: uint32) : uint32 { newVal }


        method packet(src : uint32, dst : uint32, len : uint32)
            modifies srcs`cells, dsts`cells, lens`cells, this`emittedEvents
            requires ValidArrays()
            ensures  ValidArrays()
            // Left off here. Add the proof and ensures clause that the sum of the length, 
            // for every flow, is actually equal to the total length of the flow.
            // We will probably have to deal with rollovers of the counter!
        {
            var idx : uint32 := hashn(10, seed, [src, dst]);
            assert (idx < nFlows);
            // update key arrays and get old values
            var oldSrc := LArray<uint32>.Update(srcs, idx, memval, 0, newval, src);
            var oldDst := LArray<uint32>.Update(dsts, idx, memval, 0, newval, dst);
            // check for collision
            if (oldSrc != src || oldDst != dst) {
                // collision -- reset len[idx]
                var oldLen := LArray<uint32>.Update(lens, idx, memval, 0, newval, len);
                // since there was a collision, we have to generate a record event to collector
                generate_port(collectorPort, FlowRecord(oldSrc, oldDst, oldLen));
            }
            else {
                // no collision -- just increment len[idx]
                LArray<uint32>.Set(lens, idx, incr, len);
            }
        }
    }
}