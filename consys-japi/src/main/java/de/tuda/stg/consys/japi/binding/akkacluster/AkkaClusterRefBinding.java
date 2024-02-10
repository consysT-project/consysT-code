package de.tuda.stg.consys.japi.binding.akkacluster;

import de.tuda.stg.consys.core.store.akkacluster.AkkaClusterRef;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;

class AkkaClusterRefBinding<T extends Serializable> implements Ref<T>, Serializable {
    private final AkkaClusterRef<T> ref;

    AkkaClusterRefBinding(AkkaClusterRef<T> ref) {
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