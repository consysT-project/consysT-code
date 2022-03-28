package de.tuda.stg.consys.demo.quoddy;

import com.typesafe.config.Config;
import com.typesafe.config.ConfigFactory;
import de.tuda.stg.consys.demo.DemoExecutor;

public class Demo extends DemoExecutor<QuoddyBenchmark> {
    public static void main(String[] args) throws Exception{
        new Demo().runDemo();
    }

    @Override
    protected Config benchmarkConfig() {
        var configString = "consys {\n" +
                "  bench {\n" +
                "    warmupIterations = 5\n" +
                "    measureIterations = 5\n" +
                "    operationsPerIteration = 100\n" +
                "    outputFile = \"./bench-results/mixed/quoddy\"\n" +
                "    demo {\n" +
                "      quoddy {\n" +
                "        users = 100\n" +
                "        groups = 10\n" +
                "      }\n" +
                "      type = \"op_mixed\"\n" +
                "    }\n" +
                "  }\n" +
                "}";

        return ConfigFactory.parseString(configString);
    }

    @Override
    protected Class<QuoddyBenchmark> benchmarkClass() {
        return QuoddyBenchmark.class;
    }
}
