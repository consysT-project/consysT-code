package de.tuda.stg.consys.invariants.utils;

public class InvariantUtils {

	public static boolean stateful(Object o) {
		throw new UnsupportedOperationException("the method <stateful> is only usable in constraints.");
	}

	public static boolean __merge(Object o) {
		throw new UnsupportedOperationException("the method <merge> is only usable in constraints.");
	}

	public static <T> T object(Class<T> cls, Object... fields) {
		throw new UnsupportedOperationException("the method <object> is only usable in constraints.");
	}

	private static int replicaId = 2;
	private static int numOfReplicas = 5;

	public static void setReplicaId(int i) {
		replicaId = i;
	}

	public static void setNumOfReplicas(int i) {
		numOfReplicas = i;
	}

	public static int replicaId() {
		return replicaId;
	}

	public static int numOfReplicas() {
		return numOfReplicas;
	}


	public static int[] arrayMax(int[] as, int[] bs) {
		throw new UnsupportedOperationException("the method <arrayMax> is only usable in constraints.");
	}
}
