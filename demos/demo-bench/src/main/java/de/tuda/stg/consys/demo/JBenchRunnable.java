package de.tuda.stg.consys.demo;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkRunnable;
import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.japi.Store;
import de.tuda.stg.consys.japi.TransactionContext;

public abstract class JBenchRunnable<
        Addr,
        Obj,
        TxContext extends TransactionContext<Addr, Obj, ConsistencyLevel<SStore>>,
        JStore extends Store<Addr, Obj, ConsistencyLevel<SStore>, TxContext>,
        SStore extends de.tuda.stg.consys.core.store.Store
        > implements BenchmarkRunnable {

    private final JBenchStore<Addr, Obj, TxContext, JStore, SStore> store;
    private final BenchmarkConfig config;


    protected JBenchRunnable(JBenchStore<Addr, Obj, TxContext, JStore, SStore> store, BenchmarkConfig config) {
        super();
        this.store = store;
        this.config = config;
    }

    protected JStore store() {
        return store.javaStore();
    }

    protected int processId() {
        return config.processId();
    }

    protected int numOfProcesses() {
        return config.numberOfReplicas();
    }

    protected void barrier(String name) {
        store.barrier(name, config.numberOfReplicas(), config.barrierTimeout());
    }

    protected ConsistencyLevel<SStore> getWeakLevel() {
        return store.getWeakLevel();
    }

    protected ConsistencyLevel<SStore> getStrongLevel() {
        return store.getStrongLevel();
    }

    protected ConsistencyLevel<SStore> getMixedLevel() {
        return store.getMixedLevel();
    }
}
