package de.tuda.stg.consys.demo;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkExecutor;
import de.tuda.stg.consys.bench.BenchmarkRunnableFactory;
import de.tuda.stg.consys.bench.BenchmarkStoreFactory;

public class JBenchExecutor {

    private final BenchmarkExecutor executor;
    private final BenchmarkConfig config;

    public JBenchExecutor(String name, BenchmarkConfig config, BenchmarkStoreFactory storeFactory, BenchmarkRunnableFactory runnableFactory) {
        this.config = config;
        this.executor = new BenchmarkExecutor(config, storeFactory, runnableFactory);
    }

    public BenchmarkConfig getConfig() {
        return config;
    }

    public void runBenchmark() {
        executor.runBenchmark();
    }

    public void runBenchmarkTests() {
        executor.runBenchmarkTests();
    }
}
