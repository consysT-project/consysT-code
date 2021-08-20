package de.tuda.stg.consys.invariants.examples.creditaccount;

import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;

import static de.tuda.stg.consys.utils.InvariantUtils.numOfReplicas;
import static de.tuda.stg.consys.utils.InvariantUtils.replicaId;

@ReplicatedModel
public class ReplicatedCounter {

	public int[] incs;
	public int[] decs;

	//@ public invariant (\forall int i; true; incs[i] >= 0);

	//@ ensures (\forall int i; true; incs[i] == 0);
	//@ ensures (\forall int i; true; decs[i] == 0);
	public ReplicatedCounter() {
		this.incs = new int[numOfReplicas()];
		this.decs = new int[numOfReplicas()];
	}

	//@ assignable \nothing;
	//@ ensures \result == (\sum int i; i >= 0 && i < numOfReplicas(); incs[i]) - (\sum int i; i >= 0 && i < numOfReplicas(); decs[i]);
	public int getValue() {
		int sum = 0;
		for (int v : incs) sum += v;
		for (int v : decs) sum -= v;
		return sum;
	}

	//@ requires val >= 0;
	//@ assignable incs[replicaId()];
	//@ ensures incs[replicaId()] == \old(incs[replicaId()]) + val;
	public Void increment(int val) {
		if (val < 0) throw new IllegalArgumentException();
		incs[replicaId()] += val;
		return null;
	}

	//@ requires val >= 0;
	//@ assignable decs[replicaId()];
	//@ ensures decs[replicaId()] == \old(decs[replicaId()]) + val;
	public Void decrement(int val) {
		if (val < 0) throw new IllegalArgumentException();
		decs[replicaId()] += val;
		return null;
	}

	//@ ensures (\forall int i; i >= 0 && i < numOfReplicas(); incs[i] == Math.max(\old(incs[i]), other.incs[i]) && decs[i] == Math.max(\old(decs[i]), other.decs[i]));
	public Void merge(ReplicatedCounter other) {
		for (int i = 0; i < numOfReplicas(); i++) {
			incs[i] = Math.max(incs[i], other.incs[i]);
		}
		return null;
	}
}
