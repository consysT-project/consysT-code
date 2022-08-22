package de.tuda.stg.consys.demo.messagegroups;

import com.typesafe.config.Config;
import com.typesafe.config.ConfigFactory;
import de.tuda.stg.consys.demo.DemoExecutor;

public class Demo extends DemoExecutor<MessageGroupsBenchmark> {
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
                "      messagegroups {\n" +
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
    protected Class<MessageGroupsBenchmark> benchmarkClass() {
        return MessageGroupsBenchmark.class;
    }
}
