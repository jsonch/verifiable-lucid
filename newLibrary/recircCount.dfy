include "verifiableLucid.dfy"

/* A program that counts on recirculation. */

module RecircCount refines VerifiableLucid {

    // Events
    datatype Event = 
        | pkt(src : uint32, dst : uint32)
        | count(i : uint32)

    class Program ... {
        // Array and initialization
        var pktCtr : LArray<uint32>

        constructor () 
            ensures fresh(pktCtr)
            ensures fresh(this)
            ensures pktCtr.cells == seq(8, (_ => 0))
        {   
            pktCtr := new LArray<uint32>.Create(8, 0);            
        }

        // Memops
        function incr (oldVal: uint32, incrBy: uint32) : uint32 { 
            to_uint32(oldVal + incrBy)
        }
        function memval (oldVal: uint32, unused: uint32) : uint32 { oldVal }

        // Packet handler specification: 
        //                1. pkt emits packets with source 0 to port 0, 
        //                   and all other packets to port 1.
        //                2. pkt increments pktCtr[src % 8] by 1.
        method Pkt(src : uint32, dst : uint32) 
            modifies    this`emittedEvents, this`generatedEvent
            requires readyToHandle(pkt(src, dst))
            ensures src == 0 ==> emits(0, pkt(src, dst))
            ensures src != 0 ==> emits(1, pkt(src, dst))
            ensures generates(count(src))
        {
            if (src == 0) {
                generate_port(0, pkt(src, dst));
            } else {
                generate_port(1, pkt(src, dst));
            }
            generate(count(src));
        }
        // Count increments pktCtr[i % 8], and only pktCtr[i % 8], by 1.
        method Count(i : uint32)
            modifies pktCtr`cells
            requires |pktCtr.cells| == 8 
            ensures  LArray.updated_cell(pktCtr, i % 8, (old(pktCtr.cells)[i % 8] + 1) % max32)
        {
            var count := LArray<uint32>.Get(pktCtr, i % 8, memval, 0);
            LArray<uint32>.Set(pktCtr, i % 8, incr, 1);
        }        
    }
}

