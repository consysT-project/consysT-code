package de.tuda.stg.consys.invariants.examples.tournament;

import com.google.common.collect.Sets;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import de.tuda.stg.consys.invariants.examples.gset.GSet;

@ReplicatedModel
public class TwoPhaseSetPlayer {

	public GSetPlayer adds = new GSetPlayer();
	public GSetPlayer removals = new GSetPlayer();

	//@ ensures adds.isEmpty() && removals.isEmpty();
	public TwoPhaseSetPlayer() {

	}

	//@ requires (removals.contains(obj) == false);
	//@ assignable adds;
	//@ ensures adds.contains(obj);
	//@ ensures (\forall Player elem; \old(adds.contains(elem)); adds.contains(elem));
	//@ ensures (\forall Player elem; adds.contains(elem) && elem.equals(obj) == false; \old(adds.contains(elem)));
	public void add(Player obj) {
		adds.add(obj);
	}

	//@ assignable removals;
	//@ ensures removals.contains(obj);
	//@ ensures (\forall Player elem; \old(removals.contains(elem)); removals.contains(elem));
	//@ ensures (\forall Player elem; removals.contains(elem) && elem.equals(obj) == false; \old(removals.contains(elem)));
	public void remove(Player obj) {
		removals.add(obj);
	}

	//@ assignable \nothing;
	//@ ensures \result == !removals.contains(obj) && adds.contains(obj);
	public boolean contains(Player obj){
		return !removals.contains(obj) && adds.contains(obj);
	}

	//@ assignable \nothing;
	//@ ensure \result == (\forall Player p; adds.contains(p); removals.contains(p));
	public boolean isEmpty() {
		return Sets.difference(adds.underlying, removals.underlying).isEmpty();
	}

	//@ ensures (\forall Player val; \old(adds.contains(val)) || other.adds.contains(val); this.adds.contains(val));
	//@ ensures (\forall Player val; this.adds.contains(val); \old(adds.contains(val)) || other.adds.contains(val));
	//@ ensures (\forall Player val; \old(removals.contains(val)) || other.removals.contains(val); this.removals.contains(val));
	//@ ensures (\forall Player val; this.removals.contains(val); \old(removals.contains(val)) || other.removals.contains(val));
	public Void merge(TwoPhaseSetPlayer other) {
		adds.merge(other.adds);
		removals.merge(other.removals);
		return null;
	}
}