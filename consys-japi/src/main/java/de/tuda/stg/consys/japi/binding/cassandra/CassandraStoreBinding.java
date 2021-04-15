package de.tuda.stg.consys.japi.binding.cassandra;

import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.core.store.cassandra.CassandraTransactionContext;
import de.tuda.stg.consys.japi.Store;
import de.tuda.stg.consys.japi.Transaction;
import scala.Function1;
import scala.Option;

import java.io.Serializable;

public class CassandraStoreBinding implements Store<String, Serializable, ConsistencyLevel<CassandraStore>, CassandraTransactionContextBinding> {
    private final CassandraStore store;

    CassandraStoreBinding(CassandraStore store) {
        this.store = store;
    }

    @Override
    public <U> Option<U> transaction(Transaction<CassandraTransactionContextBinding, U, String, Serializable, ConsistencyLevel<CassandraStore>> tx) {
        return store.transaction((Function1<CassandraTransactionContext, Option<U>>) v1 -> tx.doTransaction(new CassandraTransactionContextBinding(v1)));
    }

    @Override
    public void close() throws Exception {
        store.close();
    }
}