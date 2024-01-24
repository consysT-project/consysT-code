package de.tuda.stg.consys.invariants.lib.examples.tournament;

import com.google.common.collect.Sets;
import de.tuda.stg.consys.Mergeable;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;


@ReplicatedModel
public class TwoPhaseSetTournament implements Mergeable<TwoPhaseSetTournament>, Serializable {

	public GSetTournament adds = new GSetTournament();
	public GSetTournament removals = new GSetTournament();

	//@ ensures adds.isEmpty() && removals.isEmpty();
	public TwoPhaseSetTournament() {

	}

	//@ requires (removals.contains(obj) == false);
	//@ assignable adds;
	//@ ensures adds.contains(obj);
	//@ ensures (\forall Tournament elem; \old(adds.contains(elem)); adds.contains(elem));
	//@ ensures (\forall Tournament elem; adds.contains(elem) && elem.equals(obj) == false; \old(adds.contains(elem)));
	 public void add(Tournament obj) {
		adds.add(obj);
	}

	//@ assignable removals;
	//@ ensures removals.contains(obj);
	//@ ensures (\forall Tournament elem; \old(removals.contains(elem)); removals.contains(elem));
	//@ ensures (\forall Tournament elem; removals.contains(elem) && elem.equals(obj) == false; \old(removals.contains(elem)));
	 public void remove(Tournament obj) {
		removals.add(obj);
	}

	//@ assignable \nothing;
	//@ ensures \result == !removals.contains(obj) && adds.contains(obj);
	  public boolean contains(Tournament obj){
		return !removals.contains(obj) && adds.contains(obj);
	}

	//@ assignable \nothing;
	//@ ensure \result == (\forall Tournament p; adds.contains(p); removals.contains(p));
	  public boolean isEmpty() {
		return Sets.difference(adds.underlying, removals.underlying).isEmpty();
	}

	//@ ensures (\forall Tournament val; \old(adds.contains(val)) || other.adds.contains(val); this.adds.contains(val));
	//@ ensures (\forall Tournament val; this.adds.contains(val); \old(adds.contains(val)) || other.adds.contains(val));
	//@ ensures (\forall Tournament val; \old(removals.contains(val)) || other.removals.contains(val); this.removals.contains(val));
	//@ ensures (\forall Tournament val; this.removals.contains(val); \old(removals.contains(val)) || other.removals.contains(val));
	public Void merge(TwoPhaseSetTournament other) {
		adds.merge(other.adds);
		removals.merge(other.removals);
		return null;
	}
}
