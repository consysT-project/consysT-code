package de.tuda.stg.consys.japi.binding.akka;

import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.akka.AkkaRef;
import de.tuda.stg.consys.core.store.akka.AkkaStore;
import de.tuda.stg.consys.core.store.akka.AkkaTransactionContext;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.TransactionContext;

import java.io.Serializable;

public class AkkaTransactionContextBinding implements TransactionContext<String, Serializable, ConsistencyLevel<AkkaStore>> {
    private final AkkaTransactionContext ctx;

    AkkaTransactionContextBinding(AkkaTransactionContext ctx) {
        this.ctx = ctx;
    }

    @Override
    public <T extends Serializable> Ref<T> replicate(String s, ConsistencyLevel<AkkaStore> level, Class<T> clazz, Object... constructorArgs) {
        AkkaRef<T> handler = (AkkaRef<T>) ctx.replicate(s, level, clazz, constructorArgs);
        return new AkkaRefBinding<>(handler);
    }

    @Override
    public <T extends Serializable> Ref<T> lookup(String s, ConsistencyLevel<AkkaStore> level, Class<T> clazz) {
        AkkaRef<T> handler = (AkkaRef<T>) ctx.lookup(s, level, clazz);
        return new AkkaRefBinding<T>(handler);
    }
}

