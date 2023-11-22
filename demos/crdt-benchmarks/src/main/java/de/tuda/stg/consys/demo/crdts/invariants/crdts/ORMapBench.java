package de.tuda.stg.consys.demo.crdts.invariants.crdts;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.crdts.CRDTBenchRunnable;
import de.tuda.stg.consys.invariants.lib.crdts.ORMap;
import scala.Option;

import java.util.Random;

public class ORMapBench extends CRDTBenchRunnable<ORMap> {
    public static void main(String[] args) {
        JBenchExecution.execute("invariants-ormap", ORMapBench.class, args);
    }

    public ORMapBench(JBenchStore adapter, BenchmarkConfig config) {
        super(adapter, config, ORMap.class);
    }

    private Random random = new Random();

    @Override
    @SuppressWarnings("consistency")
    public BenchmarkOperations operations() {
        return BenchmarkOperations.withUniformDistribution(new Runnable[] {
                () -> store().transaction(ctx -> {
                    crdt.invoke("put", random.nextInt(99), random.nextInt(99));
                    return Option.apply(0);
                }),
                () -> store().transaction(ctx -> {
                    crdt.invoke("containsKey", random.nextInt(99));
                    return Option.apply(0);
                }),
                () -> store().transaction(ctx -> {
                    crdt.invoke("isEmpty");
                    return Option.apply(0);
                }),
                () -> store().transaction(ctx -> {
                    crdt.invoke("get", random.nextInt(99));
                    return Option.apply(0);
                }),
                () -> store().transaction(ctx -> {
                    crdt.invoke("remove", random.nextInt(99));
                    return Option.apply(0);
                })
        });
    }
}
