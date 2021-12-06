package de.tuda.stg.consys.invariants.crdtlib.gset;
// Grow-only Set CRDT

import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import static de.tuda.stg.consys.utils.InvariantUtils.numOfReplicas;
import static de.tuda.stg.consys.utils.InvariantUtils.replicaId;

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
    public Void add(T val) {
        underlying.add(val);
        return null;
    }

    //@ assignable \nothing;
    //@ ensures \result == underlying.contains(val);
    public boolean contains(T val){
        return underlying.contains(val);
    }

    //@ assignable \nothing;
    //@ ensures \result == underlying.isEmpty();
    public boolean isEmpty() {
        return underlying.isEmpty();
    }

    //@ assignable \nothing
    //@ ensures \result.equals(underlying)
    public Set<T> getValue() {
        return underlying;
    }

    //@ ensures (\forall T i; \old(underlying.contains(i)) || other.underlying.contains(i); underlying.contains(i));
    //@ ensures (\forall T i; underlying.contains(i); \old(underlying.contains(i)) || other.underlying.contains(i));
    public Void merge(GSet<T> other) {
        underlying.addAll(other.underlying);
        return null;
    }
}