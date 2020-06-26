package de.tuda.stg.consys.demo.dcrdt;

import com.typesafe.config.Config;
import com.typesafe.config.ConfigFactory;
import de.tuda.stg.consys.demo.DemoExecutor;

public class DCRDTDemo extends DemoExecutor<CounterBenchmark> {
    public static void main(String[] args) throws Exception{
        new DCRDTDemo().runDemo();
    }

    @Override
    protected Config benchmarkConfig() {
        var configString = "consys {\n" +
                "\tbench {\n" +
                "\t\tdemo {\n" +
                "\t\t\ttype = \"mixed\"\n" +
                "\t\t}\n" +
                "\t}\n" +
                "}";

        return ConfigFactory.parseString(configString);
    }

    @Override
    protected Class<CounterBenchmark> benchmarkClass() {
        return CounterBenchmark.class;
    }
}
