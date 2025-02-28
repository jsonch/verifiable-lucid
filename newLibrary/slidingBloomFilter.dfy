/*
    A sliding / multi-pane bloom filter. 

    3 panes: 
        active
        maintaining
        clearing

    packet operations: 
        query: 
            - reset next index of clearing
            - take || of all indices in active and maintaining
        insert:
            - reset next index of clearing
            - set all indices in maintaining

    the sequence property of interest: 
        - assuming that packets arrive at a fast enough rate to keep everything clear that should be clear, 
            after you insert a key k, you will be able to query it for at least cycleTime additional time units.
            In psuedocode:
                insert(k) @ t ==> forall t' :: 
                    (t < t' <= t + paneCycleTime)  ==> (query(k) @ t == true)
*/