package de.tuda.stg.consys.demo;

import de.tuda.stg.consys.objects.japi.JReplicaSystem;
import de.tuda.stg.consys.objects.japi.JReplicaSystems;

/**
 * Created on 14.03.19.
 *
 * @author Mirko Köhler
 */
public class Replicas {

	public static final JReplicaSystem replicaSystem1;
	public static final JReplicaSystem replicaSystem2;
	static {
		JReplicaSystem[] systems = JReplicaSystems.fromActorSystemForTesting(2);
		replicaSystem1 = systems[0];
		replicaSystem2 = systems[1];
	}
	
}
