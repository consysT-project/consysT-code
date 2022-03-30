package de.tuda.stg.consys.demo.twitterclone;

import com.typesafe.config.Config;
import com.typesafe.config.ConfigFactory;
import de.tuda.stg.consys.demo.DemoExecutor;

public class Demo extends DemoExecutor<TwitterCloneBenchmark> {
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
                "    outputFile = \"./bench-results/mixed/twitter\"\n" +
                "    demo {\n" +
                "      twitterclone {\n" +
                "        users = 100\n" +
                "      }\n" +
                "      type = \"op_mixed\"\n" +
                "    }\n" +
                "  }\n" +
                "}";

        return ConfigFactory.parseString(configString);
    }

    @Override
    protected Class<TwitterCloneBenchmark> benchmarkClass() {
        return TwitterCloneBenchmark.class;
    }
}
