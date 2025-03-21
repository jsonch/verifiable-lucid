/*
This implements the data plane cache of TurboFlow. 

TurboFlow is a flow telemetry system with two components: 
    - a Data plane cache measures per-flow flow counters (e.g., total packet count) 
      over short time intervals. When the cache evicts a flow, 
      it sends a record of the cached value of that flow's counter to 
      a backend collection server. 
    - The collection server aggregates records from the cache to calculate 
      the complete per flow counters.

The main property of the data plane cache is a per flow property:
    For every flow that has been seen by the system, 
    the counter in the cache + the counter in the collector 
    is equal to the true total count of the flow.

The verification strategy is to keep models of the collector and a 
"reference" store. The reference store counts all the packets. 
We verify the cach + collector count is the same as the reference count.

This property did not hold in the initial version of TurboFlow, 
because it does not deal with counter overflows in the cache.
To fix this, we add the extra exception handling case 
around line 186, where we evict a flow if its counter is in 
danger of overflowing on the next packet. 

We also add an assumption that packet lengths are always 
under a certain value.

We can also probably find bugs in TurboFlow related to: 
    - timestamp / duration overflows
    - packet loss
*/


include "verifiableLucid.dfy"

module BloomFilter refines VerifiableLucid {
    const nFlows : nat := 1024
    type  flowIdx_t = f : nat | f < 1024
    type  flowKey_t = (uint32, uint32)
    const maxPktLen : uint32 := 2048

    class ExactStore {
        ghost var flows : map<flowKey_t, nat>
        ghost constructor () 
            ensures fresh(this)
            ensures flows == map[]
        {
            flows := map[];
        }

        ghost method Update(key : flowKey_t, len : uint32)
            modifies this`flows
            ensures flows.Keys == old(flows).Keys + {key} // all old flows are still here, and the new flow too
            // all counters besides for key stay the same
            ensures forall k | k in old(flows) :: k in flows && (k != key ==> old(flows)[k] == flows[k])
            // flows[key] is incremented appropriately
            ensures if key in old(flows)
                        then key in flows && flows[key] == old(flows)[key] + len
                        else flows[key] == len
            
        {
            flows := 
                if (key in flows) then
                    flows[key := flows[key] + len]
                else
                    flows[key := len];
        }
    }

    function incr (oldVal: uint32, incrBy: uint32) : uint32 { 
        to_uint32(oldVal + incrBy)
    }

    function safeIncr (oldVal: uint32, incrBy: uint32) : uint32 {         
        // if the new counter value is above some unsafe threshold, 
        // such that the next packet may cause it to overflow, 
        // we want to evict, which means resetting it.
        if ((oldVal + incrBy) % max32) >= max32 - maxPktLen
        then incrBy
        else to_uint32(oldVal + incrBy)
    }


    function memval (oldVal: uint32, unused: uint32) : uint32 { oldVal }
    function newval (oldVal: uint32, newVal: uint32) : uint32 { newVal }

    datatype Event = 
        | Packet(src : uint32, dst : uint32, len : uint32)
        | FlowRecord(src : uint32, dst : uint32, len : uint32)

    class Program ... {
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
            && |srcs.cells| == |dsts.cells| == |lens.cells| == nFlows
            // ghost aliasing ARGH
            && this.fullStore != this.collectorStore
        }

        ghost var fullStore : ExactStore // models collector that just processes everything
        ghost var collectorStore : ExactStore // models collector that processes evicted records

        constructor ()
            ensures ValidArrays()
            ensures fullStore.flows == map[]
            ensures collectorStore.flows == map[]
        {
            srcs := new LArray<uint32>.Create(nFlows, 0);
            dsts := new LArray<uint32>.Create(nFlows, 0);
            lens := new LArray<uint32>.Create(nFlows, 0);
            ArrayRepr := {srcs, dsts, lens};
            fullStore := new ExactStore();
            collectorStore := new ExactStore();
        }

        function cacheLen(key : flowKey_t) : nat
            reads this, ArrayRepr
            requires ValidArrays()
        {
            var idx : uint32 := hashn(10, seed, [key.0, key.1]);
            if ((srcs.cells[idx] == key.0) && (dsts.cells[idx] == key.1))
            then lens.cells[idx]
            else 0
        }
        ghost function collectorLen(key : flowKey_t) : nat            
            reads this`collectorStore, this.collectorStore
        {
            if key in this.collectorStore.flows
                then this.collectorStore.flows[key]
                else 0 // not found
        }

        ghost function fullLen(key : flowKey_t) : nat
            reads this`fullStore, this.fullStore
        {            
            if key in fullStore.flows
                then fullStore.flows[key]
                else 0               
        }

        ghost predicate stateInvariant(key : flowKey_t)
            // The cache is correct for flow k if the cache counter + collector counter == full counter
            reads this, ArrayRepr
            reads this.fullStore, this.collectorStore
            requires ValidArrays()            
        {
            fullLen(key) == cacheLen(key) + collectorLen(key)
        }

        method packet(src : uint32, dst : uint32, len : uint32)
            modifies srcs`cells, dsts`cells, lens`cells, this`emittedEvents
            modifies this.fullStore, this.collectorStore // ghost
            requires this.fullStore != this.collectorStore
            requires ValidArrays()
            requires len < maxPktLen && cacheLen((src, dst)) < max32 - maxPktLen // Length correctness
            requires stateInvariant((src, dst))
            ensures  ValidArrays()
            ensures  cacheLen((src, dst)) < max32 - maxPktLen
            ensures  stateInvariant((src, dst))
            // Without the additional case that checks for a near-overflow and then evicts, 
            // only the weaker state invariant below holds
            // ensures  (old(cacheLen((src, dst))) + len as nat < max32) ==> stateInvariant((src, dst))
        {
            fullStore.Update((src, dst), len);
            var idx : uint32 := hashn(10, seed, [src, dst]);
            assert (idx < nFlows);

            var oldSrc := LArray<uint32>.Update(srcs, idx, memval, 0, newval, src);
            var oldDst := LArray<uint32>.Update(dsts, idx, memval, 0, newval, dst);         

            // check for collision and reset the counter if there is one.
            if (oldSrc != src || oldDst != dst) {
                var oldLen := LArray<uint32>.Update(lens, idx, memval, 0, newval, len);
                generate_port(collectorPort, FlowRecord(oldSrc, oldDst, oldLen));
                collectorStore.Update((oldSrc, oldDst), oldLen);
            }
            else {
                var oldLen : uint32 := LArray<uint32>.Update(lens, idx, memval, 0, safeIncr, len);
                // if the old length was too large, reset the counter.
                if ((oldLen + len)% max32 >= max32 - maxPktLen) {
                    generate_port(collectorPort, FlowRecord(oldSrc, oldDst, oldLen));
                    collectorStore.Update((oldSrc, oldDst), oldLen);
                }
            }
        }
    }
}