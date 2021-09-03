package de.tuda.stg.consys.invariants.examples.gset;

import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;

// Grow-only Set CRDT
import java.util.HashSet;
import java.util.Set;

@ReplicatedModel public class GSet<T> {

    public Set<T> underlying;

    /* Constructors */
    //@ ensures underlying.isEmpty();
    public GSet() {
        this.underlying = new HashSet<T>();
    }

    /*@
    @ assignable underlying;
    @ ensures underlying.contains(val);
    @ ensures underlying.containsAll(\old(underlying));
    @*/
    public void add(T val) {
        underlying.add(val);
    }

    //@ assignable \nothing;
    //@ ensures \result == underlying.contains(val);
    public boolean contains(T val){
        return underlying.contains(val);
    }

    //@ assignable \nothing;
    //@ underlying.isEmpty();
    public boolean isEmpty() {
        return underlying.isEmpty();
    }

    //@ ensures (\forall T i; \old(underlying.contains(i)) || other.underlying.contains(i); underlying.contains(i));
    //@ ensures (\forall T i; underlying.contains(i); \old(underlying.contains(i)) || other.underlying.contains(i));
    public void merge(GSet<T> other) {
        underlying.addAll(other.underlying);
    }
}