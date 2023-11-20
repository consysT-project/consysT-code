package de.tuda.stg.consys.invariants.lib.crdts.data;


import com.google.common.collect.Sets;
import de.tuda.stg.consys.Mergeable;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.util.Set;

@ReplicatedModel public class TwoPhaseObjectSet implements Mergeable<TwoPhaseObjectSet> {

    public GObjectSet adds = new GObjectSet();
    public GObjectSet removals = new GObjectSet();

    /* Constructor */
    //@ ensures adds.isEmpty() && removals.isEmpty();
    public TwoPhaseObjectSet() {

    }

    //@ assignable adds;
    //@ ensures adds.contains(obj);
    //@ ensures (\forall Object elem; adds.contains(elem); \old(adds.contains(elem)) || elem == obj );
    @WeakOp public Void add(Object obj) {
        adds.add(obj);
        return null;
    }

    //@ assignable removals;
    //@ ensures removals.contains(obj);
    //@ ensures (\forall Object elem; \old(removals.contains(elem)); removals.contains(elem));
    //@ ensures (\forall Object elem; removals.contains(elem) && elem.equals(obj) == false; \old(removals.contains(elem)));
    @WeakOp public Void remove(Object obj) {
        removals.add(obj);
        return null;
    }

    //@ assignable \nothing;
    //@ ensures \result == !removals.contains(obj) && adds.contains(obj);
    @SideEffectFree @WeakOp public boolean contains(Object obj){
        return !removals.contains(obj) && adds.contains(obj);
    }

    /*@
    @ assignable \nothing;
    @ ensures \result == (\forall Object val; adds.contains(val); removals.contains(val));
    @*/
    @SideEffectFree @WeakOp public boolean isEmpty() {
        return this.getValue().isEmpty();
    }

    /*@
    @ assignable \nothing;
    @ ensures (\forall Object val; adds.contains(val) && removals.contains(val) == false; \result.contains(val));
    @ ensures (\forall Object val; \result.contains(val); adds.contains(val) && removals.contains(val) == false);
    @*/
    @SideEffectFree @WeakOp public Set<Object> getValue() {
        return Sets.difference(this.adds.getValue(), this.removals.getValue());
    }

    //@ ensures (\forall Object val; \old(adds.contains(val)) || other.adds.contains(val); this.adds.contains(val));
    //@ ensures (\forall Object val; this.adds.contains(val); \old(adds.contains(val)) || other.adds.contains(val));
    //@ ensures (\forall Object val; \old(removals.contains(val)) || other.removals.contains(val); this.removals.contains(val));
    //@ ensures (\forall Object val; this.removals.contains(val); \old(removals.contains(val)) || other.removals.contains(val));
    public Void merge(TwoPhaseObjectSet other) {
        adds.merge(other.adds);
        removals.merge(other.removals);
        return null;
    }
}
