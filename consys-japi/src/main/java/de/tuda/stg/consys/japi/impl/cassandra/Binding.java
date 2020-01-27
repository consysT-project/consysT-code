package de.tuda.stg.consys.japi.impl.cassandra;

import de.tuda.stg.consys.core.store.StoreConsistencyLevel;
import de.tuda.stg.consys.core.store.cassandra.CassandraHandler;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.core.store.cassandra.CassandraTransactionContext;
import scala.Function1;
import scala.Option;
import scala.concurrent.duration.FiniteDuration;

import java.io.Serializable;

/**
 * Created on 27.01.20.
 *
 * @author Mirko Köhler
 */
public class Binding {

	static public class Cassandra {

		public static ReplicaBinding newReplica(String host, int cassandraPort, int zookeeperPort, FiniteDuration withTimeout, boolean withInitialize) {
			CassandraStore store = CassandraStore.fromAddress(host, cassandraPort, zookeeperPort, withTimeout, withInitialize);
			return new ReplicaBinding(store);
		}

		static public class ReplicaBinding implements Replica<String, Serializable, StoreConsistencyLevel, TransactionContextBinding> {
			private final CassandraStore store;

			public ReplicaBinding(CassandraStore store) {
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


		static class TransactionContextBinding implements TransactionContext<String, Serializable, StoreConsistencyLevel> {
			private final CassandraTransactionContext ctx;

			public TransactionContextBinding(CassandraTransactionContext ctx) {
				this.ctx = ctx;
			}

			@Override
			public <T extends Serializable> Ref<T> replicate(String s, T object, StoreConsistencyLevel level) {
				Class<T> objCls = (Class<T>) object.getClass();
				CassandraHandler<T> handler = (CassandraHandler<T>) ctx.replicate(s, object, objCls, level);
				return new RefBinding<>(handler);
			}

			@Override
			public <T extends Serializable> Ref<T> lookup(String s, Class<T> clazz, StoreConsistencyLevel level) {
				CassandraHandler<T> handler = (CassandraHandler<T>) ctx.lookup(s, clazz, level);
				return new RefBinding<>(handler);
			}
		}

		static class RefBinding<T extends Serializable> implements Ref<T> {
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




}

