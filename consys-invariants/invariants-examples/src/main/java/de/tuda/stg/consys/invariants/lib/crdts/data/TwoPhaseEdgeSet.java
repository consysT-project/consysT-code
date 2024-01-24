package de.tuda.stg.consys.invariants.lib.crdts.data;


import com.google.common.collect.Sets;
import de.tuda.stg.consys.Mergeable;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;
import java.util.Set;

@ReplicatedModel public class TwoPhaseEdgeSet implements Mergeable<TwoPhaseEdgeSet>, Serializable {

    public GEdgeSet adds = new GEdgeSet();
    public GEdgeSet removals = new GEdgeSet();

    /* Constructor */
    //@ ensures adds.isEmpty() && removals.isEmpty();
    public TwoPhaseEdgeSet() {

    }

    //@ assignable adds;
    //@ ensures adds.contains(obj);
    //@ ensures (\forall Edge elem; adds.contains(elem); \old(adds.contains(elem)) || elem == obj );
     public Void add(Edge obj) {
        adds.add(obj);
        return null;
    }

    //@ assignable removals;
    //@ ensures removals.contains(obj);
    //@ ensures (\forall Edge elem; \old(removals.contains(elem)); removals.contains(elem));
    //@ ensures (\forall Edge elem; removals.contains(elem) && elem.equals(obj) == false; \old(removals.contains(elem)));
     public Void remove(Edge obj) {
        removals.add(obj);
        return null;
    }

    //@ assignable \nothing;
    //@ ensures \result == !removals.contains(obj) && adds.contains(obj);
      public boolean contains(Edge obj){
        return !removals.contains(obj) && adds.contains(obj);
    }

    /*@
    @ assignable \nothing;
    @ ensures \result == (\forall Edge val; adds.contains(val); removals.contains(val));
    @*/
      public boolean isEmpty() {
        return this.getValue().isEmpty();
    }

    /*@
    @ assignable \nothing;
    @ ensures (\forall Edge val; adds.contains(val) && removals.contains(val) == false; \result.contains(val));
    @ ensures (\forall Edge val; \result.contains(val); adds.contains(val) && removals.contains(val) == false);
    @*/
      public Set<Edge> getValue() {
        return Sets.difference(this.adds.getValue(), this.removals.getValue());
    }

    //@ ensures (\forall Edge val; \old(adds.contains(val)) || other.adds.contains(val); this.adds.contains(val));
    //@ ensures (\forall Edge val; this.adds.contains(val); \old(adds.contains(val)) || other.adds.contains(val));
    //@ ensures (\forall Edge val; \old(removals.contains(val)) || other.removals.contains(val); this.removals.contains(val));
    //@ ensures (\forall Edge val; this.removals.contains(val); \old(removals.contains(val)) || other.removals.contains(val));
    public Void merge(TwoPhaseEdgeSet other) {
        adds.merge(other.adds);
        removals.merge(other.removals);
        return null;
    }
}
