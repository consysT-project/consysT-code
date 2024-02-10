package de.tuda.stg.consys.invariants.lib.examples;

import com.google.common.collect.Sets;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;

import java.util.Set;

import de.tuda.stg.consys.annotations.invariants.SetUtils;
import de.tuda.stg.consys.annotations.invariants.ArrayUtils;


@ReplicatedModel
public class Test {

	private Set<Integer> values;

	//@ ensures SetUtils.in(values, 0);
	public Test() {
		values = Sets.<Integer>newHashSet();
		values.add(0);
	}

	//@ assignable values;
	//@ ensures values == SetUtils.union(\old(values), other);
	public Void addAll(Set<Integer> other) {
		values.addAll(other);
		return null;
	}

	//@ assignable values;
	//@ ensures values == SetUtils.add(\old(values), elem);
	public Void addOne(Integer elem) {
		values.add(elem);
		return null;
	}

	//@ ensures ArrayUtils.update(values, 0, "hallo") == values;
	public int myMethod(String[] values) {
		return 0;
	}

	//@ assignable values;
	//@ ensures values == SetUtils.union(\old(values), other.values);
	public Void merge(Test other) {
		return null;
	}

}
