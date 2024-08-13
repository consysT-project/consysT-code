package de.tuda.stg.consys.japi.binding.cassandra;

import de.tuda.stg.consys.core.store.CoordinationMechanism;
import de.tuda.stg.consys.core.store.cassandra.*;
import scala.concurrent.duration.FiniteDuration;

/**
 * Created on 27.01.20.
 *
 * @author Mirko Köhler
 */
public class CassandraReplica {

	public static CassandraStoreBinding create(String host, int cassandraPort, CoordinationMechanism coordinationMechanism, String datacenter, FiniteDuration withTimeout, boolean withInitialize) {
		CassandraStore store = CassandraStore.fromAddress(host, cassandraPort, coordinationMechanism, datacenter, withTimeout, withInitialize);
		return new CassandraStoreBinding(store);
	}

	public static CassandraStoreBinding create(String host, int cassandraPort, CoordinationMechanism coordinationMechanism, FiniteDuration withTimeout, boolean withInitialize) {
		CassandraStore store = CassandraStore.fromAddress(host, cassandraPort, coordinationMechanism, "OSS-dc0", withTimeout, withInitialize);
		return new CassandraStoreBinding(store);
	}

	public static CassandraStoreBinding create(CassandraStore store) {
		return new CassandraStoreBinding(store);
	}

}
