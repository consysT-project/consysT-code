package de.tuda.stg.consys.utils;

public class InvariantUtils {

	public static boolean stateful(Object o) {
		throw new UnsupportedOperationException("stateful is only useable in constraints.");
	}

	public static boolean __merge(Object o) {
		throw new UnsupportedOperationException("merge is only useable in constraints.");
	}

	private static int replicaId = 2;
	private static String replicaName = "replica-02@192.0.0.1";
	private static int numOfReplicas = 5;

	public static void setReplicaId(int i) {
		replicaId = i;
	}

	public static void setReplicaName(String s) {
		replicaName = s;
	}

	public static void setNumOfReplicas(int i) {
		numOfReplicas = i;
	}

	public static int replicaId() {
		return replicaId;
	}

	public static String replica() {
		return replicaName;
	}

	public static int numOfReplicas() {
		return numOfReplicas;
	}
}
