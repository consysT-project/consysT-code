package de.tuda.stg.consys.demo;

import com.typesafe.config.Config;
import com.typesafe.config.ConfigFactory;
import de.tuda.stg.consys.core.store.utils.MultiPortAddress;
import scala.Option;

import java.lang.reflect.InvocationTargetException;
import java.util.Formatter;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

public abstract class DemoExecutor<T extends CassandraDemoBenchmark> {

    protected abstract Config benchmarkConfig();
    protected abstract Class<T> benchmarkClass();

    public void runDemo() {
        MultiPortAddress[] addresses = new MultiPortAddress[] {
                new MultiPortAddress("127.0.0.1", 9042, 2181),
                new MultiPortAddress("127.0.0.2", 9042, 2182),
                new MultiPortAddress("127.0.0.3", 9042, 2183),
                new MultiPortAddress("127.0.0.4", 9042, 2184),
        };

        var exec = Executors.newFixedThreadPool(addresses.length + 1);

        try {
            var benchConstructor = benchmarkClass().getDeclaredConstructor(Config.class, Option.class);

            for (int i = 0; i < addresses.length; i++) {
                var address = addresses[i];
                var config = benchmarkConfig().withFallback(createConfig(address, i, addresses.length));

                exec.submit(() -> {
                    CassandraDemoBenchmark benchmark;
                    try {
                        benchmark = benchConstructor.newInstance(config, Option.empty());
                        benchmark.runBenchmark();
                        try {
                            if (benchmark.store() != null) {
                                benchmark.store().close();
                            }
                        } catch (Exception e) {
                            System.out.println("error closing cassandra store: ");
                            e.printStackTrace();
                        }
                    } catch (InstantiationException | IllegalAccessException | InvocationTargetException e) {
                        e.printStackTrace();
                    }
                });
            }
        } catch (NoSuchMethodException e) {
            e.printStackTrace();
        } finally {
            try {
                exec.shutdown();
                exec.awaitTermination(60, TimeUnit.SECONDS);
            } catch (InterruptedException e) {
                throw new RuntimeException(e);
            }
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
