package org.conloc.invariants.utils;

public class InvariantUtils {

	public static boolean stateful(Object o) {
		throw new UnsupportedOperationException("stateful is only useable in constraints.");
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
}
