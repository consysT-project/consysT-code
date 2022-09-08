package de.tuda.stg.consys.demo.crdts;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.crdts.schema.TwoPhaseSet;
import scala.Option;

import java.util.Random;

public class TwoPhaseSetRunnable extends CRDTBenchRunnable<TwoPhaseSet> {
    public static void main(String[] args) {
        JBenchExecution.execute("crdt-twophaseset", GSetRunnable.class, args);
    }

    public TwoPhaseSetRunnable(JBenchStore adapter, BenchmarkConfig config) {
        super(adapter, config, TwoPhaseSet.class);
    }

    private Random random = new Random();

    @Override
    @SuppressWarnings("consistency")
    public BenchmarkOperations operations() {
        return BenchmarkOperations.withUniformDistribution(new Runnable[] {
                () -> store().transaction(ctx -> {
                    crdt.invoke("add", random.nextInt(42));
                    return Option.apply(0);
                }),
                () -> store().transaction(ctx -> {
                    crdt.invoke("remove", random.nextInt(42));
                    return Option.apply(0);
                }),
                () -> store().transaction(ctx -> {
                    crdt.invoke("contains", random.nextInt(42));
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
