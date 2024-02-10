package de.tuda.stg.consys.japi.binding.akkacluster;

import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.akka.AkkaRef;
import de.tuda.stg.consys.core.store.akkacluster.AkkaClusterRef;
import de.tuda.stg.consys.core.store.akkacluster.AkkaClusterStore;
import de.tuda.stg.consys.core.store.akkacluster.AkkaClusterTransactionContext;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.TransactionContext;

import java.io.Serializable;

public class AkkaClusterTransactionContextBinding implements TransactionContext<String, Serializable, ConsistencyLevel<AkkaClusterStore>> {
    private final AkkaClusterTransactionContext ctx;

    AkkaClusterTransactionContextBinding(AkkaClusterTransactionContext ctx) {
        this.ctx = ctx;
    }

    @Override
    public <T extends Serializable> Ref<T> replicate(String s, ConsistencyLevel<AkkaClusterStore> level, Class<T> clazz, Object... constructorArgs) {
        AkkaClusterRef<T> handler = (AkkaClusterRef<T>) ctx.replicate(s, level, clazz, constructorArgs);
        return new AkkaClusterRefBinding<>(handler);
    }

    @Override
    public <T extends Serializable> Ref<T> lookup(String s, ConsistencyLevel<AkkaClusterStore> level, Class<T> clazz) {
        AkkaClusterRef<T> handler = (AkkaClusterRef<T>) ctx.lookup(s, level, clazz);
        return new AkkaClusterRefBinding<T>(handler);
    }
}

