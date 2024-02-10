package de.tuda.stg.consys.demo.messagegroups;

import com.typesafe.config.Config;
import com.typesafe.config.ConfigFactory;
import de.tuda.stg.consys.demo.DemoExecutor;

public class Demo extends DemoExecutor<MessageGroupsBenchmark> {
    public static void main(String[] args) throws Exception{
        new Demo().runDemo();
    }

    @Override
    protected Config benchmarkConfig() {
        var configString = "consys {\n" +
                "  bench {\n" +
                "    demo {\n" +
                "      messagegroups {\n" +
                "        groups = 100\n" +
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
