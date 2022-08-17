package de.tuda.stg.consys.demo;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkExecutor;

public class JBenchExecutor {

    private final BenchmarkExecutor executor;
    private final BenchmarkConfig config;

    public JBenchExecutor(String name, BenchmarkConfig config, JBenchStore store, JBenchRunnable operation) {
        this.config = config;
        this.executor = new BenchmarkExecutor(store.scalaStore(), config, operation);
    }

    public BenchmarkConfig getConfig() {
        return config;
    }

    public void runBenchmark() {
        executor.runBenchmark();
    }
}
