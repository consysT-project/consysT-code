package de.tuda.stg.consys.japi.binding.cassandra;

import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.cassandra.*;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.Replica;
import de.tuda.stg.consys.japi.Transaction;
import de.tuda.stg.consys.japi.TransactionContext;
import scala.Function1;
import scala.Option;
import scala.concurrent.duration.FiniteDuration;

import java.io.Serializable;

/**
 * Created on 27.01.20.
 *
 * @author Mirko Köhler
 */
public class Cassandra {

	public static Option<CassandraStore.CassandraStoreId> currentStore() {
		return CassandraStores.getCurrentStore().map(CassandraStore::id);
	}

	public static CassandraReplicaBinding newReplica(String host, int cassandraPort, int zookeeperPort, FiniteDuration withTimeout, boolean withInitialize) {
		CassandraStore store = CassandraStore.fromAddress(host, cassandraPort, zookeeperPort, withTimeout, withInitialize);
		return new CassandraReplicaBinding(store);
	}

}






