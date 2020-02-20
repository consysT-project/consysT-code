package de.tuda.stg.consys.japi.next.binding;

import de.tuda.stg.consys.core.store.StoreConsistencyLevel;
import de.tuda.stg.consys.core.store.cassandra.*;
import de.tuda.stg.consys.japi.next.Ref;
import de.tuda.stg.consys.japi.next.Replica;
import de.tuda.stg.consys.japi.next.Transaction;
import de.tuda.stg.consys.japi.next.TransactionContext;
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

	public static Option<CassandraStoreId> currentStore() {
		return CassandraStores.getCurrentStore().map(CassandraStore::id);
	}

	public static ReplicaBinding newReplica(String host, int cassandraPort, int zookeeperPort, FiniteDuration withTimeout, boolean withInitialize) {
		CassandraStore store = CassandraStore.fromAddress(host, cassandraPort, zookeeperPort, withTimeout, withInitialize);
		return new ReplicaBinding(store);
	}

	static public class ReplicaBinding implements Replica<String, Serializable, StoreConsistencyLevel, TransactionContextBinding> {
		private final CassandraStore store;

		ReplicaBinding(CassandraStore store) {
			this.store = store;
		}

		@Override
		public <U> Option<U> transaction(Transaction<TransactionContextBinding, U, String, Serializable, StoreConsistencyLevel> tx) {
			return store.transaction((Function1<CassandraTransactionContext, Option<U>>) v1 -> tx.doTransaction(new TransactionContextBinding(v1)));
		}

		@Override
		public void close() throws Exception {
			store.close();
		}
	}


	public static class TransactionContextBinding implements TransactionContext<String, Serializable, StoreConsistencyLevel> {
		private final CassandraTransactionContext ctx;

		TransactionContextBinding(CassandraTransactionContext ctx) {
			this.ctx = ctx;
		}

		@Override
		public <T extends Serializable> Ref<T> replicate(String s, StoreConsistencyLevel level, Class<T> clazz, Object... constructorArgs) {
			CassandraHandler<T> handler = (CassandraHandler<T>) ctx.replicate(s, level, clazz, constructorArgs);
			return new RefBinding<>(handler);
		}

		@Override
		public <T extends Serializable> Ref<T> lookup(String s, Class<T> clazz, StoreConsistencyLevel level) {
			CassandraHandler<T> handler = (CassandraHandler<T>) ctx.lookup(s, level, clazz);
			return new RefBinding<>(handler);
		}
	}

	public static class RefBinding<T extends Serializable> implements Ref<T> {
		private final CassandraHandler<T> handler;

		RefBinding(CassandraHandler<T> handler) {
			this.handler = handler;
		}

		@Override
		public <R> R getField(String fieldName) {
			return null;
		}

		@Override
		public <R> R setField(String fieldName, R value) {
			return null;
		}

		@Override
		public <R> R invoke(String methodName, Object... args) {
			return handler.resolve().invoke(methodName, args);
		}
	}
}






