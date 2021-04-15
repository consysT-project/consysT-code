package de.tuda.stg.consys.japi.binding.cassandra;

import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.cassandra.CassandraRef;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.core.store.cassandra.CassandraTransactionContext;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.TransactionContext;

import java.io.Serializable;

public class CassandraTransactionContextBinding implements TransactionContext<String, Serializable, ConsistencyLevel<CassandraStore>> {
    private final CassandraTransactionContext ctx;

    CassandraTransactionContextBinding(CassandraTransactionContext ctx) {
        this.ctx = ctx;
    }

    @Override
    public <T extends Serializable> Ref<T> replicate(String s, ConsistencyLevel<CassandraStore> level, Class<T> clazz, Object... constructorArgs) {
        CassandraRef<T> handler = (CassandraRef<T>) ctx.replicate(s, level, clazz, constructorArgs);
        return new CassandraRefBinding<>(handler);
    }

    @Override
    public <T extends Serializable> Ref<T> lookup(String s, ConsistencyLevel<CassandraStore> level, Class<T> clazz) {
        CassandraRef<T> handler = (CassandraRef<T>) ctx.lookup(s, level, clazz);
        return new CassandraRefBinding<>(handler);
    }
}

