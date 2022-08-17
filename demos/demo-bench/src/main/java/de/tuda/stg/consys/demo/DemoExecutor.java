package de.tuda.stg.consys.demo;

import com.typesafe.config.Config;
import com.typesafe.config.ConfigFactory;
import de.tuda.stg.consys.core.store.utils.MultiPortAddress;
import scala.Option;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.Formatter;
import java.util.List;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;

@Deprecated
public abstract class DemoExecutor<T extends CassandraDemoBenchmark> {

    protected abstract Config benchmarkConfig();
    protected abstract Class<T> benchmarkClass();

    public void runDemo() {
        run(false);
    }

    public void runDemoWithTest() {
        run(true);
    }

    private void run(boolean withTest) {
        MultiPortAddress[] addresses = new MultiPortAddress[] {
                new MultiPortAddress("127.0.0.1", 9042, 2181),
                new MultiPortAddress("127.0.0.2", 9042, 2182),
                new MultiPortAddress("127.0.0.3", 9042, 2183),
                new MultiPortAddress("127.0.0.4", 9042, 2184),
        };

        Constructor<T> benchConstructor;
        try {
            benchConstructor = benchmarkClass().getDeclaredConstructor(Config.class, Option.class);
        } catch (NoSuchMethodException e) {
            System.err.println("Failed to initialize benchmark. Constructor not found: " + e.getMessage());
            return;
        }

        var exec = Executors.newFixedThreadPool(addresses.length + 1);
        List<Future<?>> futures = new ArrayList<>();

        for (int i = 0; i < addresses.length; i++) {
            var address = addresses[i];
            var config = benchmarkConfig().withFallback(createConfig(address, i, addresses.length));

            futures.add(exec.submit(() -> {
                CassandraDemoBenchmark benchmark;
                try {
                    benchmark = benchConstructor.newInstance(config, Option.empty());
                    benchmark.enableTestMode();

                    if (withTest) {
                        benchmark.runWarmupOnlyWithoutCleanup();
                        benchmark.test();
                        benchmark.printTestResult();
                    } else {
                        benchmark.runBenchmark();
                    }

                    // close cassandra stores
                    if (benchmark.store() != null) {
                        try {
                            benchmark.store().close();
                        } catch (Exception e) {
                            System.err.println("error closing cassandra store: " + e.getMessage());
                        }
                    }
                } catch (InstantiationException | IllegalAccessException | InvocationTargetException e) {
                    e.printStackTrace();
                }
            }));
        }

        try {
            exec.shutdown();
            exec.awaitTermination(10, TimeUnit.SECONDS);
            for (var future : futures) {
                future.get(); // gets exceptions not caught inside thread
            }
        } catch (InterruptedException | ExecutionException e) {
            throw new RuntimeException(e);
        }
    }

    private static Config createConfig(MultiPortAddress hostname, int processId, int nReplicas) {
        String baseConfigString =
                "consys {\n" +
                        "  bench {\n" +
                        "    hostname = \"%s\"\n" +
                        "    processId = %d\n" +
                        "    nReplicas = %d\n" +
                        "    warmupIterations = 1\n" +
                        "    measureIterations = 1\n" +
                        "    operationsPerIteration = 100\n" +
                        "    waitPerOperation = 0 ms\n" +
                        "    outputFile = \"./bench-results/mixed\"\n" +
                        "  }\n" +
                        "}";

        Formatter formatter = new Formatter();
        String configString = formatter.format(baseConfigString, hostname.toString(), processId, nReplicas).toString();

        return ConfigFactory.parseString(configString);
    }
}
