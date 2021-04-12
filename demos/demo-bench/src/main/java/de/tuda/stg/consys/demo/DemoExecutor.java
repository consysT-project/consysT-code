package de.tuda.stg.consys.demo;

import com.typesafe.config.Config;
import com.typesafe.config.ConfigFactory;
import de.tuda.stg.consys.core.store.utils.Address;

import java.lang.reflect.InvocationTargetException;
import java.util.Arrays;
import java.util.Formatter;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

public abstract class DemoExecutor<T extends DemoBenchmark> {

    protected abstract Config benchmarkConfig();
    protected abstract Class<T> benchmarkClass();

    public void runDemo() {
        Address[] addresses = new Address[] {
                new Address("127.0.0.1", 3443),
                new Address("127.0.0.2", 3444),
                new Address("127.0.0.3", 3445),
                new Address("127.0.0.4", 3446)
        };

        var exec = Executors.newFixedThreadPool(addresses.length + 1);

        try {
            var benchConstructor = benchmarkClass().getDeclaredConstructor(Config.class);

            for (int i = 0; i < addresses.length; i++) {
                var address = addresses[i];
                var config = benchmarkConfig().withFallback(createConfig(address, i, addresses));

                exec.submit(() -> {
                    DemoBenchmark benchmark = null;
                    try {
                        benchmark = benchConstructor.newInstance(config);
                        benchmark.runBenchmark();
                    } catch (InstantiationException e) {
                        e.printStackTrace();
                    } catch (IllegalAccessException e) {
                        e.printStackTrace();
                    } catch (InvocationTargetException e) {
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

    private static Config createConfig(Address hostname, int processId, Address[] otherReplicas) {
        String replicasString = Arrays.stream(otherReplicas)
                .map(address -> "\"" + address.toString() + "\"")
                .collect(Collectors.joining(","));


        String baseConfigString =
                "consys {\n" +
                        "  bench {\n" +
                        "    hostname = \"%s\"\n" +
                        "    processId = %d\n" +
                        "    otherReplicas = [%s]\n" +
                        "    warmupIterations = 1\n" +
                        "    measureIterations = 1\n" +
                        "    operationsPerIteration = 100\n" +
                        "    waitPerOperation = 0 ms\n" +
                        "    outputFile = \"./bench-results/mixed\"\n" +
                        "  }\n" +
                        "}";

        Formatter formatter = new Formatter();
        String configString = formatter.format(baseConfigString, hostname.toString(), processId, replicasString).toString();

        return ConfigFactory.parseString(configString);
    }


}
