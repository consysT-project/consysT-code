package de.tuda.stg.consys.demo;

import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.extensions.coordination.BarrierStore;
import de.tuda.stg.consys.japi.Store;
import scala.concurrent.duration.FiniteDuration;

public abstract class JBenchStore<StoreType extends Store> {

    private final BarrierStore scalaStore;
    private final StoreType javaStore;

    public JBenchStore(BarrierStore scalaStore, StoreType javaStore) {
        this.scalaStore = scalaStore;
        this.javaStore = javaStore;
    }

    public StoreType javaStore() {
        return javaStore;
    }

    public StoreType store() {
        return javaStore;
    }

    public BarrierStore scalaStore() {
        return scalaStore;
    }

    public void barrier(String name, int count, FiniteDuration duration) {
        scalaStore.barrier(name, count, duration);
    }


    public abstract ConsistencyLevel getWeakLevel();

    public abstract ConsistencyLevel getStrongLevel();

    public abstract ConsistencyLevel getMixedLevel();
}
