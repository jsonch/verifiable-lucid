include "verifiableLucid.dfy"

/*  A simple program with a counting packet forwarder 
    and a query event that causes a report event to be generated.
    This program only verifies properties about individual handlers, 
    using pre and post conditions. So there are no "event sequence"
    methods, and the "readyToHandle(event)" predicate is not used. */

module CountQuery refines VerifiableLucid {

    // Events
    datatype Event = 
        | pkt(src : uint32, dst : uint32)
        | getCount(i : uint32)
        | countReport(i : uint32, count : uint32)

    class VerifiableLucidProgram ... {
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
            modifies    this`emittedEvents, this.pktCtr`cells    
            requires |pktCtr.cells| == 8 // size of pktCtr array -- 8 cells
            ensures  LArray.updated_cell(pktCtr, src % 8, (old(pktCtr.cells)[src % 8] + 1) % max32)
            ensures         ((src == 0) ==> emits(0, pkt(src, dst)))
                        &&  ((src != 0) ==> emits(1, pkt(src, dst)))
        {
            if (src == 0) {
                generate_port(0, pkt(src, dst));
            } else {
                generate_port(1, pkt(src, dst));
            }
            LArray<uint32>.Set(pktCtr, src % 8, incr, 1);
        }

        // count query specification
        // getCount emits a countReport event with the count of packets in pktCtr[i % 8].
        method GetCount(i : uint32)
            modifies this`emittedEvents
            requires |pktCtr.cells| == 8
            ensures emits(0, countReport(i, old(pktCtr.cells)[i % 8]))
        {
            var count := LArray<uint32>.Get(pktCtr, i % 8, memval, 0);
            generate_port(0, countReport(i, count));
        }        
    }
}

