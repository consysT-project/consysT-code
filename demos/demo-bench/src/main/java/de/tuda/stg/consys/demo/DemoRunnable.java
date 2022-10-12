package de.tuda.stg.consys.demo;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.core.store.ConsistencyLevel;

import java.util.*;
import java.util.function.Supplier;

public abstract class DemoRunnable extends JBenchRunnable {
    protected enum BenchmarkType {
        WEAK, MIXED, STRONG, OP_MIXED
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

    protected ConsistencyLevel getLevelWithMixedFallback(ConsistencyLevel mixedLevel) {
        switch (benchType) {
            case WEAK: return getWeakLevel();
            case STRONG: return getStrongLevel();
            case OP_MIXED: return getMixedLevel();
            case MIXED: return mixedLevel;
            default: throw new UnsupportedOperationException("unknown bench type");
        }
    }

    private final Map<String, List<Boolean>> checkResults = new HashMap<>();
    private final Map<String, List<String>> checkResultsMessage = new HashMap<>();

    public void check(String name, Supplier<Boolean> code) {
        putCheck(name, code.get());
    }

    public void check(String name, boolean result) {
        putCheck(name, result);
    }

    public <T> void checkEquals(String name, T expected, T actual) {
        boolean result = expected.equals(actual);
        putCheck(name, result);
        if (!result) {
            checkResultsMessage.putIfAbsent(name, new ArrayList<>());
            checkResultsMessage.get(name).add("expected: " + expected + ", but actual: " + actual);
        }
    }

    public void checkFloatEquals(String name, float expected, float actual) {
        checkFloatEquals(name, expected, actual, 0.000001f);
    }
    public void checkFloatEquals(String name, float expected, float actual, float eps) {
        boolean result = Math.abs(expected - actual) < eps;
        putCheck(name, result);
        if (!result) {
            checkResultsMessage.putIfAbsent(name, new ArrayList<>());
            checkResultsMessage.get(name).add("expected: " + expected + ", but actual: " + actual);
        }
    }

    private void putCheck(String name, boolean result) {
        checkResults.putIfAbsent(name, new ArrayList<>());
        checkResults.get(name).add(result);
    }

    public void printTestResult() {
        if (processId() != 0) return;

        long nFailedChecks = checkResults.values().stream().flatMap(Collection::stream).filter(b -> !b).count();

        System.out.println("- TEST RESULTS ---------");
        System.out.println("Failed checks (" + nFailedChecks + "/" + checkResults.values().stream().mapToLong(Collection::size).sum() + "):");
        for (var pair : checkResults.entrySet()) {
            nFailedChecks = pair.getValue().stream().filter(b -> !b).count();
            if (nFailedChecks > 0) {
                System.out.println("  " + pair.getKey() + " (failed " + nFailedChecks + "/" + pair.getValue().size() + ")");
                if (checkResultsMessage.containsKey(pair.getKey())) {
                    for (String msg : checkResultsMessage.get(pair.getKey()))
                        System.out.println("     " + msg);
                }
            }
        }
        System.out.println("------------------------");
    }
}
