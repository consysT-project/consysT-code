package de.tuda.stg.consys.japi.legacy;

import java.util.Set;

/**
 * Created on 13.01.20.
 *
 * @author Mirko Köhler
 */
public interface JReplicaSystemWithRemove extends JReplicaSystem {

	void remove(String addr);

	void clear(Set<String> except);

	void clear();
}
