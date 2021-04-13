package de.tuda.stg.consys.japi.legacy;

import java.time.Duration;

/**
 * Created on 13.01.20.
 *
 * @author Mirko Köhler
 */
public interface JReplicaSystemWithBarrier extends JReplicaSystem {

	void barrier(String name);

	void barrier(String name, Duration timeout);
}
