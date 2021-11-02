import bench.DemoUtils;
import org.apache.commons.io.FileUtils;

import javax.tools.JavaCompiler;
import javax.tools.ToolProvider;
import java.io.File;
import java.io.IOException;
import java.util.ArrayList;

/**
 * Compile-time Benchmark
 */
public class Main {
    static int nWarmup = 5;
    static int nMeasure = 20;
    static String demosPath = "./src/main/java/demos/";

    // The old ConSysT type checker must be compiled separately under a different name to measure
    // The working directory must be thesis-test
    public static void main(String[] args) {
        System.out.println("### Counter ###");
        System.out.println(" > Java:");
        compileJava("counter", nMeasure, nWarmup);
        //System.out.println(" > ConSysT:");
        //compileConSysT("counter", nMeasure, nWarmup);
        System.out.println(" > ConSysTOp:");
        compileConSysTOp("counter", nMeasure, nWarmup);

        System.out.println("### Twitter ###");
        System.out.println(" > Java:");
        compileJava("twitter", nMeasure, nWarmup);
        //System.out.println(" > ConSysT:");
        //compileConSysT("twitter", nMeasure, nWarmup);
        System.out.println(" > ConSysTOp:");
        compileConSysTOp("twitter", nMeasure, nWarmup);

        System.out.println("### Messages ###");
        System.out.println(" > Java:");
        compileJava("message", nMeasure , nWarmup);
        //System.out.println(" > ConSysT:");
        //compileConSysT("message", nMeasure, nWarmup);
        System.out.println(" > ConSysTOp:");
        compileConSysTOp("message", nMeasure, nWarmup);

        System.out.println("### Bank ###");
        System.out.println(" > Java:");
        compileJava("bank", nMeasure, nWarmup);
        //System.out.println(" > ConSysT:");
        //compileConSysT("bank", nMeasure, nWarmup);
        System.out.println(" > ConSysTOp:");
        compileConSysTOp("bank", nMeasure, nWarmup);
    }

    private static void compileJava(String path, int m, int w) {
        // warmup
        for (int i = 0; i < w; i++) {
            compile("-d", "out",
                    "@" + demosPath + path + "/java/files");
            delete();
        }

        // measure
        var times = new ArrayList<Double>(m);
        for (int i = 0; i < m; i++) {
            times.add(compile("-d", "out",
                    "@" + demosPath + path + "/java/files"));
            delete();
        }
        DemoUtils.printResult(times);
    }

    private static void compileConSysT(String path, int m, int w) {
        // warmup
        for (int i = 0; i < m; i++) {
            compile("-d", "out",
                    "-processor", "de.tuda.stg.consys.checker.TestConsistencyChecker",
                    "-AsuppressWarnings=inconsistent.constructor.type,cast.unsafe",
                    "@" + demosPath + path + "/consyst/files");
            delete();
        }

        // measure
        var times = new ArrayList<Double>(m);
        for (int i = 0; i < m; i++) {
            times.add(compile("-d", "out",
                    "-processor", "de.tuda.stg.consys.checker.TestConsistencyChecker",
                    "-AsuppressWarnings=inconsistent.constructor.type,cast.unsafe",
                    "@" + demosPath + path + "/consyst/files"));
            delete();
        }
        DemoUtils.printResult(times);
    }

    private static void compileConSysTOp(String path, int m, int w) {
        // warmup
        for (int i = 0; i < w; i++) {
            compile("-d", "out",
                    "-processor", "de.tuda.stg.consys.checker.ConsistencyChecker",
                    "-Astubs=./src/main/resources/List.astub;./src/main/resources/Cassandra.astub",
                    "-AsuppressWarnings=inconsistent.constructor.type,cast.unsafe",
                    "@" + demosPath + path + "/consystop/files");
            delete();
        }

        // measure
        var times = new ArrayList<Double>(m);
        for (int i = 0; i < m; i++) {
            times.add(compile("-d", "out",
                    "-processor", "de.tuda.stg.consys.checker.ConsistencyChecker",
                    "-Astubs=./src/main/resources/List.astub;./src/main/resources/Cassandra.astub",
                    "-AsuppressWarnings=inconsistent.constructor.type,cast.unsafe",
                    "@" + demosPath + path + "/consystop/files"));
            delete();
        }
        DemoUtils.printResult(times);
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
}
