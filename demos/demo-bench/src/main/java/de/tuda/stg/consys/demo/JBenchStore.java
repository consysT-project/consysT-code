package de.tuda.stg.consys.demo;

import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.extensions.coordination.BarrierStore;
import de.tuda.stg.consys.japi.Store;
import de.tuda.stg.consys.japi.TransactionContext;
import scala.concurrent.duration.FiniteDuration;

public abstract class JBenchStore<
        Addr,
        Obj,
        TxContext extends TransactionContext<Addr, Obj, ConsistencyLevel<SStore>>,
        JStore extends Store<Addr, Obj, ConsistencyLevel<SStore>, TxContext>,
        SStore extends de.tuda.stg.consys.core.store.Store
        > {

    private final BarrierStore scalaStore;
    private final JStore javaStore;

    public JBenchStore(BarrierStore scalaStore, JStore javaStore) {
        this.scalaStore = scalaStore;
        this.javaStore = javaStore;
    }

    public JStore javaStore() {
        return javaStore;
    }

    public JStore store() {
        return javaStore;
    }

    public BarrierStore scalaStore() {
        return scalaStore;
    }

    public void barrier(String name, int count, FiniteDuration duration) {
        scalaStore.barrier(name, count, duration);
    }


    public abstract ConsistencyLevel<SStore> getWeakLevel();

    public abstract ConsistencyLevel<SStore> getStrongLevel();

    public abstract ConsistencyLevel<SStore> getMixedLevel();
}
