package de.tuda.stg.consys.invariants.examples.creditaccount;

import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;

import static de.tuda.stg.consys.utils.InvariantUtils.numOfReplicas;
import static de.tuda.stg.consys.utils.InvariantUtils.replicaId;

@ReplicatedModel
public class ReplicatedCounter {

	public int[] values;

	//@ ensures (\forall int i; true; values[i] == 0);
	public ReplicatedCounter() {
		this.values = new int[numOfReplicas()];
	}

	//@ assignable \nothing;
	//@ ensures \result == (\sum int i; i >= 0 && i < numOfReplicas(); values[i]);
	public int getValue() {
		int sum = 0;
		for (int v : values) sum += v;
		return sum;
	}

	//@ requires val >= 0;
	//@ assignable values[replicaId()];
	//@ ensures values[replicaId()] == \old(values[replicaId()]) + val;
	public Void increment(int val) {
		if (val < 0) throw new IllegalArgumentException();
		values[replicaId()] += val;
		return null;
	}

	//@ ensures (\forall int i; i >= 0 && i < numOfReplicas(); values[i] == Math.max(\old(values[i]), other.values[i]));
	public Void merge(ReplicatedCounter other) {
		for (int i = 0; i < numOfReplicas(); i++) {
			values[i] = Math.max(values[i], other.values[i]);
		}
		return null;
	}
}
