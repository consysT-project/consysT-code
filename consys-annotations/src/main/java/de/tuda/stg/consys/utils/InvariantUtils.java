package de.tuda.stg.consys.utils;

public class InvariantUtils {

	public static boolean stateful(Object o) {
		throw new UnsupportedOperationException("stateful is only useable in constraints.");
	}

	public static int replicaId() {
		return 2; //TODO implement
	}

	public static String replica() {
		return "replica-02@192.0.0.1"; //TODO implement
	}

	public static int numOfReplicas() {
		return 3; //TODO implement
	}
}
