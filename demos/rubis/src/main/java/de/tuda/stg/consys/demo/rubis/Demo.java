package de.tuda.stg.consys.demo.rubis;

import com.typesafe.config.Config;
import com.typesafe.config.ConfigFactory;
import de.tuda.stg.consys.demo.DemoExecutor;

public class Demo extends DemoExecutor<RubisBenchmark> {
    public static void main(String[] args) throws Exception{
        new Demo().runDemo();
    }

    @Override
    protected Config benchmarkConfig() {
        var configString = "consys {\n" +
                "  bench {\n" +
                "    warmupIterations = 1\n" +
                "    measureIterations = 1\n" +
                "    operationsPerIteration = 100\n" +
                "    outputFile = \"./bench-results/mixed/rubis\"\n" +
                "    demo {\n" +
                "      rubis {\n" +
                "        users = 100\n" +
                "      }\n" +
                "      type = \"op_mixed\"\n" +
                "    }\n" +
                "  }\n" +
                "}";

        return ConfigFactory.parseString(configString);
    }

    @Override
    protected Class<RubisBenchmark> benchmarkClass() {
        return RubisBenchmark.class;
    }
}
