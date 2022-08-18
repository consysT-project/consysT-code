package de.tuda.stg.consys.demo;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkRunnable;
import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.extensions.ClearableStore;
import de.tuda.stg.consys.japi.Store;

public abstract class JBenchRunnable<StoreType extends Store> implements BenchmarkRunnable {

    private final JBenchStore<StoreType> store;
    private final BenchmarkConfig config;


    protected JBenchRunnable(JBenchStore<StoreType> store, BenchmarkConfig config) {
        super();
        this.store = store;
        this.config = config;
    }

    protected StoreType store() {
        return store.javaStore();
    }

    protected int processId() {
        return config.processId();
    }

    protected void barrier(String name) {
        store.barrier(name, config.numberOfReplicas(), config.barrierTimeout());
    }

    protected ConsistencyLevel getWeakLevel() {
        return store.getWeakLevel();
    }

    protected ConsistencyLevel getStrongLevel() {
        return store.getStrongLevel();
    }




}
