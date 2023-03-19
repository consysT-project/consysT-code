package de.tuda.stg.consys.demo;

import org.apache.commons.io.FileUtils;

import javax.tools.JavaCompiler;
import javax.tools.ToolProvider;
import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

public class CompilerBench {
    static int nWarmup = 5;
    static int nMeasure = 10;
    static String demosPath = "./demos/rubis/src/main/java/de/tuda/stg/consys/demo/rubis/schema/";

    public static void main(String[] args) {
        compileJava("sequential", nMeasure, nWarmup);
        System.out.println("----------");
        compileConSys("opcentric", nMeasure, nWarmup);
    }

    private static void compileJava(String path, int m, int w) {
        // warmup
        for (int i = 0; i < w; i++) {
            compile("-d", "out",
                    "@" + demosPath + path + "/files");
            delete();
        }

        // measure
        var times = new ArrayList<Double>(m);
        for (int i = 0; i < m; i++) {
            times.add(compile("-d", "out",
                    "@" + demosPath + path + "/files"));
            delete();
        }

        printResult(times);
    }

    private static void compileConSys(String path, int m, int w) {
        // warmup
        for (int i = 0; i < w; i++) {
            compile("-d", "out",
                    "-processor", "de.tuda.stg.consys.checker.ConsistencyChecker",
                    "-AsuppressWarnings=inconsistent.constructor.type,cast.unsafe",
                    "@" + demosPath + path + "/files");
            delete();
        }

        // measure
        var times = new ArrayList<Double>(m);
        for (int i = 0; i < m; i++) {
            times.add(compile("-d", "out",
                    "-processor", "de.tuda.stg.consys.checker.ConsistencyChecker",
                    "-AsuppressWarnings=inconsistent.constructor.type,cast.unsafe",
                    "@" + demosPath + path + "/files"));
            delete();
        }

        printResult(times);
    }

    private static double compile(String... args) {
        JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();

        final long start = System.currentTimeMillis();
        final int result = compiler.run(null, null, null, args);
        final long duration = System.currentTimeMillis() - start;

        if (result != 0)
            throw new RuntimeException("compile error");

        return duration / 1000.;
    }

    private static void delete() {
        try {
            FileUtils.deleteDirectory(new File("./out"));
        } catch (IOException e) {
            System.out.println("delete error");
        }
    }

    static void printResult(List<Double> values) {
        values.sort(Double::compare);
        double mean = values.stream().reduce(0., Double::sum) / values.size();
        double median = values.get(values.size()/2);
        double s = Math.sqrt(values.stream().map(x -> (x-mean)*(x-mean)).reduce(0., Double::sum) / (values.size()-1));
        double range = values.get(values.size()-1) - values.get(0);

        System.out.println("      mean:   " + mean);
        System.out.println("      median: " + median);
        System.out.println("      s:      " + s);
        System.out.println("      range:  " + range);
    }
}
