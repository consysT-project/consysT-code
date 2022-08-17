package de.tuda.stg.consys.demo.crdts.schema;
// Two-phase Set CRDT (Remove wins Sets also)

import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Sets;
import de.tuda.stg.consys.Mergeable;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;

import java.io.Serializable;

@SuppressWarnings("consistency")
@ReplicatedModel public class TwoPhaseSet<T> implements Mergeable<TwoPhaseSet<T>>, Serializable {

    public GSet<T> adds = new GSet<T>();
    public GSet<T> removals = new GSet<T>();

    /* Constructor */
    //@ ensures adds.isEmpty() && removals.isEmpty();
    public TwoPhaseSet() {

    }

    //@ requires (removals.contains(obj) == false);
    //@ assignable adds;
    //@ ensures adds.contains(obj);
    //@ ensures (\forall T elem; \old(adds.contains(elem)); adds.contains(elem));
    //@ ensures (\forall T elem; adds.contains(elem) && elem.equals(obj) == false; \old(adds.contains(elem)));
    public Void add(T obj) {
        adds.add(obj);
        return null;
    }

    //@ assignable removals;
    //@ ensures removals.contains(obj);
    //@ ensures (\forall T elem; \old(removals.contains(elem)); removals.contains(elem));
    //@ ensures (\forall T elem; removals.contains(elem) && elem.equals(obj) == false; \old(removals.contains(elem)));
    public Void remove(T obj) {
        removals.add(obj);
        return null;
    }

    //@ assignable \nothing;
    //@ ensures \result == !removals.contains(obj) && adds.contains(obj);
    public boolean contains(T obj){
        return !removals.contains(obj) && adds.contains(obj);
    }

    /*@
    @ assignable \nothing;
    @ ensures \result == (\forall T val; adds.contains(val); removals.contains(val));
    @*/
    public boolean isEmpty() {
        return this.getValue().isEmpty();
    }

    /*@
    @ assignable \nothing;
    @ ensures (\forall T val; adds.contains(val) && removals.contains(val) == false; \result.contains(val));
    @ ensures (\forall T val; \result.contains(val); adds.contains(val) && removals.contains(val) == false);
    @*/
    public ImmutableSet<T> getValue() {
        return ImmutableSet.copyOf(Sets.difference(this.adds.getValue(), this.removals.getValue()));
    }

    //@ ensures (\forall T val; \old(adds.contains(val)) || other.adds.contains(val); this.adds.contains(val));
    //@ ensures (\forall T val; this.adds.contains(val); \old(adds.contains(val)) || other.adds.contains(val));
    //@ ensures (\forall T val; \old(removals.contains(val)) || other.removals.contains(val); this.removals.contains(val));
    //@ ensures (\forall T val; this.removals.contains(val); \old(removals.contains(val)) || other.removals.contains(val));
    public Void merge(TwoPhaseSet<T> other) {
        adds.merge(other.adds);
        removals.merge(other.removals);
        return null;
    }
}
