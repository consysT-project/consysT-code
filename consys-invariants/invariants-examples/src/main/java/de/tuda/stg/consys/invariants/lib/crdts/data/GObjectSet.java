package de.tuda.stg.consys.invariants.lib.crdts.data;

import de.tuda.stg.consys.Mergeable;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.HashSet;
import java.util.Set;

@ReplicatedModel public class GObjectSet implements Mergeable<GObjectSet>, Serializable {

    public Set<Object> underlying;

    /* Constructors */
    //@ ensures underlying.isEmpty();
    public GObjectSet() {
        this.underlying = new HashSet<Object>();
    }


    //@ assignable underlying;
    //@ ensures underlying.contains(val);
    //@ ensures underlying.containsAll(\old(underlying));
    @WeakOp public Void add(Object val) {
        underlying.add(val);
        return null;
    }

    //@ assignable \nothing;
    //@ ensures \result == underlying.contains(val);
    @SideEffectFree @WeakOp public boolean contains(Object val){
        return underlying.contains(val);
    }

    //@ assignable \nothing;
    //@ ensures \result == underlying.isEmpty();
    @SideEffectFree @WeakOp public boolean isEmpty() {
        return underlying.isEmpty();
    }

    //@ assignable \nothing;
    //@ ensures \result.equals(underlying);
    @SideEffectFree @WeakOp public Set<Object> getValue() {
        return underlying;
    }

    //@ ensures (\forall Object i; \old(underlying.contains(i)) || other.underlying.contains(i); underlying.contains(i));
    //@ ensures (\forall Object i; underlying.contains(i); \old(underlying.contains(i)) || other.underlying.contains(i));
    public Void merge(GObjectSet other) {
        underlying.addAll(other.underlying);
        return null;
    }
}