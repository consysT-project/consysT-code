package de.tuda.stg.consys.japi.binding.akkacluster;

import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.akkacluster.AkkaClusterStore;
import de.tuda.stg.consys.core.store.akkacluster.AkkaClusterTransactionContext;
import de.tuda.stg.consys.japi.Store;
import de.tuda.stg.consys.japi.Transaction;
import scala.Function1;
import scala.Option;

import java.io.Serializable;

public class AkkaClusterStoreBinding implements Store<String, Serializable, ConsistencyLevel<AkkaClusterStore>, AkkaClusterTransactionContextBinding> {
    private final AkkaClusterStore store;

    AkkaClusterStoreBinding(AkkaClusterStore store) {
        this.store = store;
    }

    @Override
    public <U> Option<U> transaction(Transaction<AkkaClusterTransactionContextBinding, U, String, Serializable, ConsistencyLevel<AkkaClusterStore>> tx) {
        return store.transaction((Function1<AkkaClusterTransactionContext, Option<U>>) v1 -> tx.doTransaction(new AkkaClusterTransactionContextBinding(v1)));
    }

    public void addOtherReplica(String hostname, int akkaPort) {
        store.addOtherReplica(hostname, akkaPort);
    }

    @Override
    public String getId() {
        return store.id().uniqueAddress().toString();
    }

    @Override
    public void close() throws Exception {
        store.close();
    }

    @Override
    public void clear() {
        store.clear();
    }
}