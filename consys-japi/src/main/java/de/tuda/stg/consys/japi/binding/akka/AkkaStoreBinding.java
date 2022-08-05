package de.tuda.stg.consys.japi.binding.akka;

import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.akka.AkkaStore;
import de.tuda.stg.consys.core.store.akka.AkkaTransactionContext;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.core.store.cassandra.CassandraTransactionContext;
import de.tuda.stg.consys.japi.Store;
import de.tuda.stg.consys.japi.Transaction;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;
import scala.Function1;
import scala.Option;

import java.io.Serializable;

public class AkkaStoreBinding implements Store<String, Serializable, ConsistencyLevel<AkkaStore>, AkkaTransactionContextBinding> {
    private final AkkaStore store;

    AkkaStoreBinding(AkkaStore store) {
        this.store = store;
    }

    @Override
    public <U> Option<U> transaction(Transaction<AkkaTransactionContextBinding, U, String, Serializable, ConsistencyLevel<AkkaStore>> tx) {
        return store.transaction((Function1<AkkaTransactionContext, Option<U>>) v1 -> tx.doTransaction(new AkkaTransactionContextBinding(v1)));
    }

    public void addOtherReplica(String hostname, int akkaPort) {
        store.addOtherReplica(hostname, akkaPort);
    }

    public String getId() {
        return store.id();
    }

    @Override
    public void close() throws Exception {
        store.close();
    }
}