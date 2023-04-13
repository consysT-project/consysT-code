package de.tuda.stg.consys.invariants.lib;

import de.tuda.stg.consys.invariants.OnlyUsableInConstraintsException;

import java.util.Set;

public class SetUtils {

	public static <A> Set<A> emptySet() {
		throw new OnlyUsableInConstraintsException();
	};

	public static <A, A1 extends A, A2 extends A> Set<A> union(Set<A1> set1, Set<A2> set2) {
		throw new OnlyUsableInConstraintsException();
	}
}
