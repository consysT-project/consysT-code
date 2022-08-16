package de.tuda.stg.consys.demo;

import de.tuda.stg.consys.bench.BaseStoreBenchmarkConfig;
import de.tuda.stg.consys.bench.StoreBenchmarkConfig;
import de.tuda.stg.consys.bench.StoreBenchmarkExecutor;
import de.tuda.stg.consys.core.store.Store;

public class JBenchExecutor {

    private final StoreBenchmarkExecutor executor;
    private final StoreBenchmarkConfig config;

    private final JBenchOperation operation;

    private final JBenchStore store;

    public JBenchExecutor(String name, StoreBenchmarkConfig config, JBenchStore store, JBenchOperation operation) {
        this.config = config;
        this.store = store;
        this.operation = operation;
        this.executor = new StoreBenchmarkExecutor(store.scalaStore(), config, operation);
    }

    public StoreBenchmarkConfig getConfig() {
        return config;
    }

    public void runBenchmark() {
        executor.runBenchmark();
    }



//    public static JBenchExecutor load(String name, String configName, JBenchStoreFactory adapterFactory, JStoreBenchmarkOpsFactory opsFactory, BenchmarkStoreFactories.BenchmarkStoreFactory storeFactory) {
//        var config = new BaseStoreBenchmarkConfig(name, configName, storeFactory);
//        var store = adapterFactory.create((Store) config.store());
//
//        var operation = opsFactory.create(store, config);
//
//        var executor = new StoreBenchmarkExecutor(config, operation);
//    }


}
