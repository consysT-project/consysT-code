package de.tuda.stg.consys.demo.concert;

import de.tuda.stg.consys.objects.japi.JReplicaSystem;
import de.tuda.stg.consys.objects.japi.JReplicaSystems;

public class Replicas {
	public static final JReplicaSystem replicaSystem1 = JReplicaSystems.fromActorSystem(2552);
	public static final JReplicaSystem replicaSystem2 = JReplicaSystems.fromActorSystem(2553);

	static {
		replicaSystem1.addReplicaSystem("127.0.0.1", 2553);
		replicaSystem2.addReplicaSystem("127.0.0.1", 2552);
	}
}
