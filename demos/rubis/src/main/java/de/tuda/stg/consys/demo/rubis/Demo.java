package de.tuda.stg.consys.demo.rubis;

import com.typesafe.config.Config;
import com.typesafe.config.ConfigFactory;
import de.tuda.stg.consys.demo.DemoExecutor;

public class Demo extends DemoExecutor<RubisBenchmark> {
    public static void main(String[] args) {
        if (args.length > 0 && args[0].equals("-test"))
            new Demo().runDemoWithTest();
        else
            new Demo().runDemo();
    }

    @Override
    protected Config benchmarkConfig() {
        var configString = "consys {\n" +
                "  bench {\n" +
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
