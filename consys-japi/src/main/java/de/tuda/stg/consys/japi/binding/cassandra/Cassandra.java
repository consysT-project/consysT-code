package de.tuda.stg.consys.japi.binding.cassandra;

import de.tuda.stg.consys.core.store.cassandra.*;
import scala.Option;
import scala.concurrent.duration.FiniteDuration;

/**
 * Created on 27.01.20.
 *
 * @author Mirko Köhler
 */
public class Cassandra {

	public static Option<CassandraStore.CassandraStoreId> currentStore() {
		return CassandraStores.getCurrentStore().map(CassandraStore::id);
	}

	public static CassandraStoreBinding newReplica(String host, int cassandraPort, int zookeeperPort, FiniteDuration withTimeout, boolean withInitialize) {
		CassandraStore store = CassandraStore.fromAddress(host, cassandraPort, zookeeperPort, withTimeout, withInitialize);
		return new CassandraStoreBinding(store);
	}

}






