package de.tuda.stg.consys.demo;

import de.tuda.stg.consys.bench.StoreBenchmarkConfig;
import de.tuda.stg.consys.bench.StoreBenchmarkOps;
import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.japi.Store;

public abstract class JStoreBenchmarkOps<StoreType extends Store> implements StoreBenchmarkOps {

    private final JStoreAdapter<StoreType> adapter;
    private final StoreBenchmarkConfig config;


    protected JStoreBenchmarkOps(JStoreAdapter<StoreType> adapter, StoreBenchmarkConfig config) {
        super();
        this.adapter = adapter;
        this.config = config;
    }

    protected StoreType store() {
        return adapter.store();
    }

    protected int processId() {
        return config.processId();
    }

    protected void barrier(String name) {
        adapter.barrier(name, config.numberOfReplicas(), config.barrierTimeout());
    }

    protected ConsistencyLevel getWeakLevel() {
        return adapter.getWeakLevel();
    }

    protected ConsistencyLevel getStrongLevel() {
        return adapter.getStrongLevel();
    }




}
