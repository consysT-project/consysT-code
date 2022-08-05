package de.tuda.stg.consys.japi.binding.akka;

import de.tuda.stg.consys.core.store.akka.AkkaRef;
import de.tuda.stg.consys.core.store.cassandra.CassandraRef;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;

class AkkaRefBinding<T extends Serializable> implements Ref<T>, Serializable {
    private final AkkaRef<T> ref;

    AkkaRefBinding(AkkaRef<T> ref) {
        this.ref = ref;
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