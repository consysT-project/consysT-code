package de.tuda.stg.consys.invariants.lib.examples;

import com.google.common.collect.Sets;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;

import static de.tuda.stg.consys.invariants.lib.SetUtils.emptySet;
import static de.tuda.stg.consys.invariants.lib.SetUtils.union;

import java.util.Set;

@ReplicatedModel
public class Test {

	private Set<Integer> values;

	//@ ensures values.isEmpty();
	public Test() {
		values = Sets.<Integer>newHashSet();
	}

	//@ assignable values;
	//@ ensures values == union(\old(values), other);
	public Void addAll(Set<Integer> other) {
		values.addAll(other);
		return null;
	}



	public Void merge(Test other) {
		return null;
	}

}
