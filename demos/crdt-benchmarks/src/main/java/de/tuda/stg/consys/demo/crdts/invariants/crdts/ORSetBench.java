package de.tuda.stg.consys.demo.crdts.invariants.crdts;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.crdts.CRDTBenchRunnable;
import de.tuda.stg.consys.invariants.lib.crdts.ORSet;
import scala.Option;

import java.util.Random;

public class ORSetBench extends CRDTBenchRunnable<ORSet> {
    public static void main(String[] args) {
        JBenchExecution.execute("invariants-orset", ORSetBench.class, args);
    }

    public ORSetBench(JBenchStore adapter, BenchmarkConfig config) {
        super(adapter, config, ORSet.class);
    }

    private Random random = new Random();

    @Override
    @SuppressWarnings("consistency")
    public BenchmarkOperations operations() {
        return BenchmarkOperations.withUniformDistribution(new Runnable[] {
                () -> store().transaction(ctx -> {
                    crdt.invoke("add", random.nextInt(99));
                    return Option.apply(0);
                }),
                () -> store().transaction(ctx -> {
                    crdt.invoke("remove", random.nextInt(99));
                    return Option.apply(0);
                }),
                () -> store().transaction(ctx -> {
                    crdt.invoke("contains", random.nextInt(99));
                    return Option.apply(0);
                }),
                () -> store().transaction(ctx -> {
                    crdt.invoke("isEmpty");
                    return Option.apply(0);
                }),
                () -> store().transaction(ctx -> {
                    crdt.invoke("getValue");
                    return Option.apply(0);
                })
        });
    }
}
