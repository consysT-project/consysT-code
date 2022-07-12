//package de.tuda.stg.consys.demo.concert;
//
//import com.typesafe.config.Config;
//import com.typesafe.config.ConfigFactory;
//import de.tuda.stg.consys.demo.legacy.DemoExecutor;
//
//public class Demo extends DemoExecutor<ConcertBenchmark> {
//    public static void main(String[] args) throws Exception{
//        new Demo().runDemo();
//    }
//
//    @Override
//    protected Config benchmarkConfig() {
//        var configString = "consys {\n" +
//                "\tbench {\n" +
//                "\t\tdemo {\n" +
//                "\t\t\ttype = \"mixed\"\n" +
//                "\t\t}\n" +
//                "\t}\n" +
//                "}";
//
//        return ConfigFactory.parseString(configString);
//    }
//
//    @Override
//    protected Class<ConcertBenchmark> benchmarkClass() {
//        return ConcertBenchmark.class;
//    }
//}
