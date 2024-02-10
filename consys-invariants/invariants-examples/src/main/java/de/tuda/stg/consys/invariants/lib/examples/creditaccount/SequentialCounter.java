package de.tuda.stg.consys.invariants.lib.examples.creditaccount;

import de.tuda.stg.consys.annotations.invariants.DataModel;

@DataModel
public class SequentialCounter {

	private int value;

	//@ ensures value == initial;
	public SequentialCounter(int initial) {
		this.value = initial;
	}

	//@ assignable \nothing;
	//@ ensures \result == value;
	public int getValue() {
		return value;
	}

	//@ requires val >= 0;
	//@ assignable value;
	//@ ensures value == \old(value) + val;
	public Void increment(int val) {
		if (val < 0) throw new IllegalArgumentException();
		value += val;
		return null;
	}

	//@ requires val >= 0;
	//@ assignable value;
	//@ ensures value == \old(value) - val;
	public Void decrement(int val) {
		if (val < 0) throw new IllegalArgumentException();
		value -= val;
		return null;
	}

	//@ assignable value;
	//@ ensures value == val;
	public Void setValue(int val) {
		value = val;
		return null;
	}
}
