package de.tuda.stg.consys.invariants.crdtlib;

import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;


public interface Mergeable<T> {
    Void merge(T o);
}
