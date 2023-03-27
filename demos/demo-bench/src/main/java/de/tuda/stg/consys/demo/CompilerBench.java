package de.tuda.stg.consys.demo;

import org.apache.commons.io.FileUtils;
import org.checkerframework.org.apache.commons.lang3.ArrayUtils;

import javax.tools.JavaCompiler;
import javax.tools.ToolProvider;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Stream;

public class CompilerBench {
    static int nWarmup = 20;
    static int nMeasure = 30;
    static List<String> basePaths = Arrays.asList(
            "./demos/counter/src/main/java/de/tuda/stg/consys/demo/counter/schema/",
            "./demos/twitter-clone/src/main/java/de/tuda/stg/consys/demo/twitterclone/schema/",
            "./demos/message-groups/src/main/java/de/tuda/stg/consys/demo/messagegroups/schema/",
            "./demos/rubis/src/main/java/de/tuda/stg/consys/demo/rubis/schema/",
            "./demos/quoddy/src/main/java/de/tuda/stg/consys/demo/quoddy/schema/"
    );

    public static void main(String[] args) throws IOException {
        for (var basePath : basePaths) {
            System.out.println(basePath);
            System.out.println("  > java:");
            compileJava(basePath, nMeasure, nWarmup);
            System.out.println("  > consys:");
            compileConSys(basePath, nMeasure, nWarmup);
        }
    }

    private static void compileJava(String path, int m, int w) throws IOException {
        // warmup
        for (int i = 0; i < w; i++) {
            compile(ArrayUtils.addAll(new String[] {"-d", "./out/"}, listFiles(path)));
            delete();
        }

        // measure
        var times = new ArrayList<Double>(m);
        for (int i = 0; i < m; i++) {
            times.add(compile(ArrayUtils.addAll(new String[] {"-d", "./out/"}, listFiles(path))));
            delete();
        }

        printResult(times);
    }

    private static void compileConSys(String path, int m, int w) throws IOException {
        // warmup
        for (int i = 0; i < w; i++) {
            compile(ArrayUtils.addAll(new String[] {
                    "-d", "./out/",
                    "-processor", "de.tuda.stg.consys.checker.ConsistencyChecker",
                    //"-processor", "org.checkerframework.checker.tainting.TaintingChecker",
                    "-AsuppressWarnings=inconsistent.constructor.type,cast.unsafe"
            }, listFiles(path)));
            delete();
        }

        // measure
        var times = new ArrayList<Double>(m);
        for (int i = 0; i < m; i++) {
            times.add(compile(ArrayUtils.addAll(new String[] {
                    "-d", "./out/",
                    "-processor", "de.tuda.stg.consys.checker.ConsistencyChecker",
                    //"-processor", "org.checkerframework.checker.tainting.TaintingChecker",
                    "-AsuppressWarnings=inconsistent.constructor.type,cast.unsafe"
            }, listFiles(path))));
            delete();
        }

        printResult(times);
    }

    private static String[] listFiles(String path) throws IOException {
        try (Stream<Path> stream = Files.walk(Paths.get(path))) {
            return stream.filter(Files::isRegularFile).map(Path::toString).toArray(String[]::new);
        }
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
            FileUtils.deleteDirectory(new File("./out/"));
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
