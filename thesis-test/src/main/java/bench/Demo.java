package bench;

import de.tuda.stg.consys.japi.binding.cassandra.Cassandra;
import scala.concurrent.duration.Duration;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;

/**
 * Run-time benchmark, runs on local cassandra cluster
 */
public class Demo {
    static int nWarmup = 5; // 5
    static int nMeasure = 20; // 5
    static int nOperations = 100;

    public static void main(String[] args) throws Exception {
        // get logging warnings out of the way
        var dummy = Cassandra.newReplica("127.0.0.1", 9042, 2181, Duration.apply(60, "s"), true);
        dummy.close();

        System.out.println("### Counter ###");
        runCounterDemo();
        System.out.println("### Twitter ###");
        runTwitterDemo();
        System.out.println("### Messages ###");
        runMessageGroupDemo();
        System.out.println("### Bank ###");
        runBankDemo();

        System.exit(0);
    }

    static void runCounterDemo() throws InterruptedException {
        var mixed = Arrays.asList(
                new CounterDemo.Mixed(),
                new CounterDemo.Mixed(),
                new CounterDemo.Mixed());
        System.out.println(" > Counter (ConSysT-Op):");
        System.out.println(run(mixed, nWarmup, nMeasure, nOperations));

        var mono = Arrays.asList(
                new CounterDemo.Mono(),
                new CounterDemo.Mono(),
                new CounterDemo.Mono());
        System.out.println(" > Counter (ConSysT):");
        System.out.println(run(mono, nWarmup, nMeasure, nOperations));
    }

    static void runMessageGroupDemo() throws InterruptedException {
        var mixed = Arrays.asList(
                new MessageDemo.Mixed(),
                new MessageDemo.Mixed(),
                new MessageDemo.Mixed());
        System.out.println(" > Message Groups (ConSysT-Op):");
        System.out.println(run(mixed, nWarmup, nMeasure, nOperations));

        var mono = Arrays.asList(
                new MessageDemo.Mono(),
                new MessageDemo.Mono(),
                new MessageDemo.Mono());
        System.out.println(" > Message Groups (ConSysT):");
        System.out.println(run(mono, nWarmup, nMeasure, nOperations));
    }

    static void runTwitterDemo() throws InterruptedException {
        var mixed = Arrays.asList(
                new TwitterDemo.Mixed(),
                new TwitterDemo.Mixed(),
                new TwitterDemo.Mixed());
        System.out.println(" > Twitter (ConSysT-Op):");
        System.out.println(run(mixed, nWarmup, nMeasure, nOperations));

        var mono = Arrays.asList(
                new TwitterDemo.Mono(),
                new TwitterDemo.Mono(),
                new TwitterDemo.Mono());
        System.out.println(" > Twitter (ConSysT):");
        System.out.println(run(mono, nWarmup, nMeasure, nOperations));
    }

    static void runBankDemo() throws InterruptedException {
        int nOperations = 100;

        var mixed = Arrays.asList(
                new BankDemo.Mixed(),
                new BankDemo.Mixed(),
                new BankDemo.Mixed());
        System.out.println(" > Bank (Mixed):");
        System.out.println(run(mixed, nWarmup, nMeasure, nOperations));

        var mono = Arrays.asList(
                new BankDemo.Mono(),
                new BankDemo.Mono(),
                new BankDemo.Mono());
        System.out.println(" > Bank (ConSysT):");
        System.out.println(run(mono, nWarmup, nMeasure, nOperations));
    }

    static String run(List<? extends Bench> benches, int nWarmup, int nMeasure, int opsPerIteration) throws InterruptedException {
        // warmup
        System.out.print("   warmup");
        for (int j = 0; j < nWarmup; j++) {
            // setup
            for (int i = 0; i < benches.size(); i++) {
                benches.get(i).setup(i);
            }
            runBenches(benches, opsPerIteration);
            // shutdown
            for (Bench bench : benches) {
                bench.shutdown();
            }
            System.out.print(".");
        }
        System.out.print("\n");

        // measure
        String result = "";
        //double sum = 0;
        var times = new ArrayList<Double>(nMeasure);
        System.out.print("   measure");
        for (int j = 0; j < nMeasure; j++) {
            // setup
            for (int i = 0; i < benches.size(); i++) {
                benches.get(i).setup(i);
            }
            double time = runBenches(benches, opsPerIteration);
            // shutdown
            for (Bench bench : benches) {
                bench.shutdown();
            }
            System.out.print(".");
            times.add(time);
        }
        System.out.print("\n");
        DemoUtils.printResult(times);
        return result;
    }

    static double runBenches(List<? extends Bench> benches, int nOperations) throws InterruptedException {
        var pool = Executors.newFixedThreadPool(3);
        final long start = System.currentTimeMillis();
        List<Future> futures = new LinkedList<>() {};
        for (var bench : benches) {
            futures.add(pool.submit(() -> {
                for (int i = 0; i < nOperations; i++) {
                    bench.operation();
                }
            }));
        }
        pool.shutdown();
        pool.awaitTermination(5, TimeUnit.MINUTES);
        for (var future: futures) {
            try {
                future.get();
            } catch (ExecutionException e) {
                e.printStackTrace();
                return -1;
            }
        }

        final long duration = System.currentTimeMillis() - start;
        return duration / 1000.;
    }
}

/*
Zipf distributions:
for N=2:
    1: 0.66 | 1
    2: 0.33 | 0.33
for N=3
    1: 0.54 | 1
    2: 0.27 | 0.45
    3: 0.18 | 0.18
for N=4
    1: 0.48 | 1
    2: 0.24 | 0.52
    3: 0.16 | 0.28
    4: 0.12 | 0.12
for N=5
    1: 0.43 | 1
    2: 0.21 | 0.53
    3: 0.14 | 0.32
    4: 0.10 | 0.18
    5: 0.08 | 0.08
*/