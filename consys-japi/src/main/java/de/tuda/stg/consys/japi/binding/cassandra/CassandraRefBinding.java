package de.tuda.stg.consys.japi.binding.cassandra;

import de.tuda.stg.consys.core.store.cassandra.CassandraRef;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;

class CassandraRefBinding<T extends Serializable> implements Ref<T> {
    private final CassandraRef<T> ref;

    CassandraRefBinding(CassandraRef<T> handler) {
        this.ref = handler;
    }

    @Override
    public <R> R getField(String fieldName) {
        return ref.resolve().getField(fieldName);
    }

    @Override
    public <R> void setField(String fieldName, R value) {
        ref.resolve().setField(fieldName, value);
    }

    @Override
    public <R> R invoke(String methodName, Object... args) {
        return ref.resolve().invoke(methodName, args);
    }
}