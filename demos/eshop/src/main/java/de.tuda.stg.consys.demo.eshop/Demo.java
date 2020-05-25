package de.tuda.stg.consys.demo.eshop;

import com.typesafe.config.Config;
import com.typesafe.config.ConfigFactory;
import de.tuda.stg.consys.demo.DemoExecutor;

public class Demo extends DemoExecutor<EShopBenchmark> {
    public static void main(String[] args) throws Exception{
        new Demo().runDemo();
    }

    @Override
    protected Config benchmarkConfig() {
        var configString = "consys {\n" +
                "  bench {\n" +
                "    demo {\n" +
                "      eshop {\n" +
                "        products = 100\n" +
                "        users = 1000\n" +
                "      }\n" +
                "      type = \"mixed\"\n" +
                "    }\n" +
                "  }\n" +
                "}";

        return ConfigFactory.parseString(configString);
    }

    @Override
    protected Class<EShopBenchmark> benchmarkClass() {
        return EShopBenchmark.class;
    }
}
