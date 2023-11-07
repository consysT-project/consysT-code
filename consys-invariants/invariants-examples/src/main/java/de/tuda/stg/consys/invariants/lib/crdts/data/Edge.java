package de.tuda.stg.consys.invariants.lib.crdts.data;

import de.tuda.stg.consys.annotations.invariants.DataModel;

@DataModel
public class Edge {

    public final Object from;
    public final Object to;

    public Edge(Object from, Object to) {
        this.from = from;
        this.to = to;
    }
}
