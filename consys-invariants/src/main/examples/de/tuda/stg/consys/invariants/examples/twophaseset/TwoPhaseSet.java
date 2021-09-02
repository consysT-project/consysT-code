package de.tuda.stg.consys.invariants.examples.twophaseset;

import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import de.tuda.stg.consys.invariants.examples.gset.GSet;

@ReplicatedModel
public class TwoPhaseSet<T>{

	public GSet<T> adds = new GSet<>();
	public GSet<T> removals = new GSet<>();

	//@ ensures adds.isEmpty() && removals.isEmpty();
	public TwoPhaseSet() {

	}

	//@ requires (removals.contains(obj) == false);
	//@ assignable adds;
	//@ ensures adds.contains(obj);
	//@ ensures (\forall T elem; \old(adds.contains(elem)); adds.contains(elem));
	//@ ensures (\forall T elem; adds.contains(elem) && elem.equals(obj) == false; \old(adds.contains(elem)));
	public void add(T obj) {
		adds.add(obj);
	}

	//@ assignable removals;
	//@ ensures removals.contains(obj);
	//@ ensures (\forall T elem; \old(removals.contains(elem)); removals.contains(elem));
	//@ ensures (\forall T elem; removals.contains(elem) && elem.equals(obj) == false; \old(removals.contains(elem)));
	public void remove(T obj) {
		removals.add(obj);
	}

	//@ assignable \nothing;
	//@ ensures \result == !removals.contains(obj) && adds.contains(obj);
	public boolean contains(T obj){
		return !removals.contains(obj) && adds.contains(obj);
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
