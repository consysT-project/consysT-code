package de.tuda.stg.consys.AuctionsSystem;

import de.tuda.stg.consys.japi.JReplicaSystem;
import de.tuda.stg.consys.japi.impl.JReplicaSystems;

/**
 * Created on 15.01.20.
 *
 * @author Mirko Köhler
 */
public class Replicas {
	private static final JReplicaSystem[] systems = JReplicaSystems.fromActorSystemForTesting(2);

	public static final JReplicaSystem replicaSystem1 = systems[0];
	public static final JReplicaSystem replicaSystem2 = systems[1];
}
