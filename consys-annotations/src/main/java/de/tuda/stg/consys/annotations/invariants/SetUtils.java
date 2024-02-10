package de.tuda.stg.consys.annotations.invariants;


import java.util.Set;

public class SetUtils {

	public static <A> Set<A> emptySet() {
		throw new OnlyUsableInConstraintsException();
	};

	public static <A> Set<A> union(Set<A> set1, Set<A> set2) {
		throw new OnlyUsableInConstraintsException();
	}

	public static <A> boolean in(Set<A> set1, A element) {
		throw new OnlyUsableInConstraintsException();
	}

	public static <A> Set<A> add(Set<A> set1, A element) {
		throw new OnlyUsableInConstraintsException();
	}
}
