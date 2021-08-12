package de.tuda.stg.consys.invariants.examples.gset;

import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;

// Grow-only Set CRDT
import java.util.HashSet;
import java.util.Set;

@ReplicatedModel public class GSet {

    public Set<Integer> underlying;

    /* Constructors */
    //@ ensures underlying.isEmpty();
    public GSet() {
        this.underlying = new HashSet<Integer>();
    }

    /*@
    @ assignable underlying;
    @ ensures underlying.contains(val);
    @ ensures underlying.containsAll(\old(underlying));
    @*/
    void add(int val) {
        underlying.add(val);
    }

    /*@
    @ assignable \nothing;
    @ ensures \result == underlying.contains(val);
    @*/
    boolean contains(int val){
        return underlying.contains(val);
    }

    /*@
    @ ensures (\forall int i; \old(underlying.contains(i)) || other.underlying.contains(i); underlying.contains(i));
    @ ensures (\forall int i; underlying.contains(i); \old(underlying.contains(i)) || other.underlying.contains(i));
    @*/
    void merge(GSet other) {
        underlying.addAll(other.underlying);
    }
}