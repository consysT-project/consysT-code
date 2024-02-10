package de.tuda.stg.consys.annotations.invariants;


import java.util.Set;

public class ArrayUtils {

	public static int[] update(int[] array, int index, int newVal) {
		throw new OnlyUsableInConstraintsException();
	};

	public static <A> A[] update(A[] array, int index, A newVal) {
		throw new OnlyUsableInConstraintsException();
	};

}
