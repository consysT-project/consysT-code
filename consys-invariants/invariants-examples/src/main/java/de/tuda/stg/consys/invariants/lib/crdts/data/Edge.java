package de.tuda.stg.consys.invariants.lib.crdts.data;

import de.tuda.stg.consys.annotations.invariants.DataModel;

import java.io.Serializable;

@DataModel
public class Edge implements Serializable {

    public final Object from;
    public final Object to;

    public Edge(Object from, Object to) {
        this.from = from;
        this.to = to;
    }
}
