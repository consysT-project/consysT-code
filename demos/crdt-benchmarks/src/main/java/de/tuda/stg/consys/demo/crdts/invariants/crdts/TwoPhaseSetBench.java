package de.tuda.stg.consys.demo.crdts.invariants.crdts;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.crdts.CRDTBenchRunnable;
import de.tuda.stg.consys.invariants.lib.crdts.TwoPhaseSet;
import scala.Option;

import java.util.Random;

public class TwoPhaseSetBench extends CRDTBenchRunnable<TwoPhaseSet> {
    public static void main(String[] args) {
        JBenchExecution.execute("invariants-twophaseset", TwoPhaseSetBench.class, args);
    }

    public TwoPhaseSetBench(JBenchStore adapter, BenchmarkConfig config) {
        super(adapter, config, TwoPhaseSet.class);
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
