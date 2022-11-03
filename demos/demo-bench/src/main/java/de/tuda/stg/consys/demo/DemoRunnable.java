package de.tuda.stg.consys.demo;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.core.store.ConsistencyLevel;

import java.util.*;
import java.util.function.Supplier;

public abstract class DemoRunnable extends JBenchRunnable {
    protected enum BenchmarkType {
        WEAK, MIXED, STRONG, OP_MIXED, WEAK_DATACENTRIC, STRONG_DATACENTRIC
    }

    protected final BenchmarkType benchType;

    protected final int nReplicas;

    protected boolean isTestMode = false;

    // utility for benchmarks
    protected final Random random = new Random();

    public DemoRunnable(JBenchStore adapter, BenchmarkConfig config) {
        super(adapter, config);

        String typeString = config.toConfig().getString("consys.bench.demo.type");
        if (typeString == null) {
            throw new IllegalArgumentException("config key not found: consys.bench.demo.type");
        }

        benchType = BenchmarkType.valueOf(typeString.toUpperCase());
        nReplicas = config.numberOfReplicas();
    }

    @Override
    public void enableTests() {
        isTestMode = true;
    }

    protected String procName() {
        return "proc-" + processId();
    }

    protected ConsistencyLevel getLevelWithMixedFallback(ConsistencyLevel mixedLevel) {
        switch (benchType) {
            case WEAK:
            case WEAK_DATACENTRIC: return getWeakLevel();
            case STRONG:
            case STRONG_DATACENTRIC: return getStrongLevel();
            case OP_MIXED: return getMixedLevel();
            case MIXED: return mixedLevel;
            default: throw new UnsupportedOperationException("unknown bench type");
        }
    }

    public void check(String name, Supplier<Boolean> code) {
        TestCollector.check(name, code);
    }

    public void check(String name, boolean result) {
        TestCollector.check(name, result);
    }

    public <T> void checkEquals(String name, T expected, T actual) {
        TestCollector.checkEquals(name, expected, actual);
    }

    public void checkFloatEquals(String name, float expected, float actual) {
        TestCollector.checkFloatEquals(name, expected, actual);
    }
    public void checkFloatEquals(String name, float expected, float actual, float eps) {
        TestCollector.checkFloatEquals(name, expected, actual, eps);
    }

    public void printTestResult() {
        TestCollector.printTestResult();
    }
}
