package de.tuda.stg.consys.invariants.lib.crdts.data;

import de.tuda.stg.consys.annotations.invariants.DataModel;

@DataModel
public class Edge<V> {

    public final V from;
    public final V to;

    public Edge(V from, V to) {
        this.from = from;
        this.to = to;
    }
}
