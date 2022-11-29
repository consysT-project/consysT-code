package de.tuda.stg.consys.demo;

import java.util.*;
import java.util.function.Supplier;

public class TestCollector {
    private static final Map<String, List<Boolean>> checkResults = new HashMap<>();
    private static final Map<String, List<String>> checkResultsMessages = new HashMap<>();

    public static synchronized void clear() {
        checkResults.clear();
        checkResultsMessages.clear();
    }

    public static synchronized void check(String name, Supplier<Boolean> code) {
        putCheck(name, code.get());
    }

    public static synchronized void check(String name, boolean result) {
        putCheck(name, result);
    }

    public static synchronized <T> void checkEquals(String name, T expected, T actual) {
        boolean result = expected.equals(actual);
        putCheck(name, result);
        if (!result) {
            checkResultsMessages.putIfAbsent(name, new ArrayList<>());
            checkResultsMessages.get(name).add("expected: " + expected + ", but actual: " + actual);
        }
    }

    public static synchronized void checkFloatEquals(String name, float expected, float actual) {
        checkFloatEquals(name, expected, actual, 0.000001f);
    }
    public static synchronized void checkFloatEquals(String name, float expected, float actual, float eps) {
        boolean result = Math.abs(expected - actual) < eps;
        putCheck(name, result);
        if (!result) {
            checkResultsMessages.putIfAbsent(name, new ArrayList<>());
            checkResultsMessages.get(name).add("expected: " + expected + ", but actual: " + actual);
        }
    }

    private static synchronized void putCheck(String name, boolean result) {
        checkResults.putIfAbsent(name, new ArrayList<>());
        checkResults.get(name).add(result);
    }

    public static synchronized void printTestResult() {
        long nChecks = checkResults.values().stream().mapToLong(Collection::size).sum();
        long nFailedChecks = checkResults.values().stream().flatMap(Collection::stream).filter(b -> !b).count();

        var sb = new StringBuilder();
        sb.append("- TEST RESULTS ---------\n");
        sb.append("  Failed checks (").append(nFailedChecks).append("/").append(nChecks).append("):\n");

        for (var pair : checkResults.entrySet()) {
            nFailedChecks = pair.getValue().stream().filter(b -> !b).count();
            if (nFailedChecks > 0) {
                sb.append("    ").append(pair.getKey()).append(" (failed ").append(nFailedChecks).append("/").append(pair.getValue().size()).append(")\n");
                if (checkResultsMessages.containsKey(pair.getKey())) {
                    for (String msg : checkResultsMessages.get(pair.getKey()))
                        sb.append("     ").append(msg).append("\n");
                }
            }
        }

        System.out.println(sb);
    }
}
