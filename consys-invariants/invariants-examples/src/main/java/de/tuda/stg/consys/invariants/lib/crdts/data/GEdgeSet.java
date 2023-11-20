package de.tuda.stg.consys.invariants.lib.crdts.data;

import de.tuda.stg.consys.Mergeable;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.util.HashSet;
import java.util.Set;

@ReplicatedModel public class GEdgeSet implements Mergeable<GEdgeSet> {

    public Set<Edge> underlying;

    /* Constructors */
    //@ ensures underlying.isEmpty();
    public GEdgeSet() {
        this.underlying = new HashSet<Edge>();
    }


    //@ assignable underlying;
    //@ ensures underlying.contains(val);
    //@ ensures underlying.containsAll(\old(underlying));
    @WeakOp public Void add(Edge val) {
        underlying.add(val);
        return null;
    }

    //@ assignable \nothing;
    //@ ensures \result == underlying.contains(val);
    @SideEffectFree @WeakOp public boolean contains(Edge val){
        return underlying.contains(val);
    }

    //@ assignable \nothing;
    //@ ensures \result == underlying.isEmpty();
    @SideEffectFree @WeakOp public boolean isEmpty() {
        return underlying.isEmpty();
    }

    //@ assignable \nothing;
    //@ ensures \result.equals(underlying);
    @SideEffectFree @WeakOp public Set<Edge> getValue() {
        return underlying;
    }

    //@ ensures (\forall Edge i; \old(underlying.contains(i)) || other.underlying.contains(i); underlying.contains(i));
    //@ ensures (\forall Edge i; underlying.contains(i); \old(underlying.contains(i)) || other.underlying.contains(i));
    public Void merge(GEdgeSet other) {
        underlying.addAll(other.underlying);
        return null;
    }
}