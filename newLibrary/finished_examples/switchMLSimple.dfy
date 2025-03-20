/*
    Minimal implementation of switchML's switch-side in-network aggregator.

    Verified properties that: 
        1. aggregation loop increments to correct values
        2. generate an aggregate chunk send when an offset is complete

    The interesting thing here is that the memory layout on the 
    switch is reversed of how you would intuitively implement. 
    Verification helps us reason that the behavior is the same 
    as a simpler reference model.
    We can illustrate this more clearly in the program, and this might be 
    a nice program to use as an example in a slide deck.
*/

include "verifiableLucid.dfy"

module BloomFilter refines VerifiableLucid {

    const nWorkers := 8
    const nParams := 32 // number of arrays
    const nSlots := 256 // size of all arrays
    type paramList = s : seq<uint32> | |s| == nParams witness *


    datatype Event = 
        | ParametersChunk(worker : uint32,  offset : uint32, slot : uint32, params : paramList)
        | SendAggChunk(offset : uint32, slot : uint32, params : paramList) 
            // broadcast out to all workers when aggregation is complete

    class Program ... {
        var counts : LArray<uint32>  // |slot|
        var pool : seq<LArray<uint32>> // param x slot
        ghost var ArrayRepr : set<object>
        ghost predicate ValidArrays()
            reads this, ArrayRepr
        {
            // Repr contents
                (ArrayRepr == (set arr | arr in pool) + {counts})
            // Non-aliasing
            &&  (forall j, k :: 0 <= j < |pool| && 0 <= k < |pool| && j != k ==> pool[j] != pool[k])
            &&  (forall arr :: arr in pool ==> counts != arr)
            // Array sizes
            &&  |pool| == nParams
            &&  (forall arr :: arr in pool ==> |arr.cells| == nSlots)    
            &&  |counts.cells| == nSlots
        }

        constructor ()
            ensures ValidArrays()
            ensures fresh(this)
        {
            counts := new LArray.Create(nSlots, 0);
            pool := [];            
            new;
            pool := CreateArrayVec(nSlots, nParams, 0);
            ArrayRepr := (set p | p in pool) + {counts};
        }

        function incr (mv: uint32, incrBy: uint32) : uint32 { 
            to_uint32(mv + incrBy) 
        }
        function memval (mv: uint32, unused: uint32) : uint32 { mv }


        twostate predicate SlotIncremented(slot : uint32, params : paramList)
            // The appropriate memory areas have been incremented for the slot
            reads ArrayRepr, this
            requires ValidArrays ()
            requires slot < nSlots
        {   
                |pool| == |old(pool)|
                && (forall i :: 0 <= i < nParams ==> |pool[i].cells| == |old(pool[i].cells)|)
                && forall i :: 0 <= i < nParams ==> 
                    pool[i].cells[slot] == (old(pool[i].cells[slot]) + params[i]) % max32
        }


        // Handle one chunk of the parameter update from one worker for one slot (which is at a particular offset).
        // Generate an aggregate chunk at that offset after receiving updates from all workers.
        // Note: workers manage offset to slot mapping
        method parametersChunk(worker : uint32,  offset : uint32, slot : uint32, params : paramList)
            modifies ArrayRepr, this`generatedEvent
            requires this.generatedEvent == None()
            requires ValidArrays()
            requires slot < nSlots
            ensures  ValidArrays()
            // The slot gets incremented correctly
            ensures  SlotIncremented(slot, params)
            // We generate an event to send an aggregate chunk to all the workers
            ensures  (counts.cells[slot] == nWorkers) ==> generatedEvent.Some? && generatedEvent.v.SendAggChunk?
        {
            var aggParams : paramList := seq(nParams, _ => 0);
            label LSTART:
            for i := 0 to nParams
                invariant ValidArrays ()
                invariant 0 <= i <= nParams
                invariant forall j :: 0 <= j < i ==> // updated param cells
                    pool[j].cells[slot] == (old@LSTART(pool[j].cells[slot]) + params[j]) % max32
                invariant forall j :: i <= j < nParams ==> // param cells yet to be updated
                    pool[j].cells[slot] == old@LSTART(pool[j].cells[slot])
                // output parameter vector
                invariant forall j :: 0 <= j < i ==> aggParams[j] ==  pool[j].cells[slot]
                invariant forall j :: i <= j < nParams ==> aggParams[j] == 0                
                invariant generatedEvent == None() // we don't generate an event inside the loop
            {
                var v := LArray<uint32>.Update(pool[i], slot, incr, params[i], incr, params[i]);
                aggParams := aggParams[i:=v];
            }
            var ct : uint32 := LArray<uint32>.Update(counts, slot, incr, 1, incr, 1);
            if (ct == nWorkers) {
                generate(SendAggChunk(offset, slot, aggParams));
            }
        }
    }


}