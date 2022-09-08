package de.tuda.stg.consys.demo.crdts;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.crdts.schema.PNCounter;
import scala.Option;

import java.util.Random;

public class PNCounterRunnable extends CRDTBenchRunnable<PNCounter> {

    public static void main(String[] args) {
        JBenchExecution.execute("crdt-pncounter", PNCounterRunnable.class, args);
    }

    public PNCounterRunnable(JBenchStore adapter, BenchmarkConfig config) {
        super(adapter, config, PNCounter.class);
    }

    private Random random = new Random();

    @Override
    @SuppressWarnings("consistency")
    public BenchmarkOperations operations() {
        // One operation will be chosen randomly.
        return BenchmarkOperations.withUniformDistribution(new Runnable[] {
                () -> store().transaction(ctx -> {
                    crdt.invoke("inc");
                    return Option.apply(0);
                }),
                () -> store().transaction(ctx -> {
                    crdt.invoke("inc", random.nextInt(42));
                    return Option.apply(0);
                }),
                () -> store().transaction(ctx -> {
                    crdt.invoke("dec");
                    return Option.apply(0);
                }),
                () -> store().transaction(ctx -> {
                    crdt.invoke("dec", random.nextInt(42));
                    return Option.apply(0);
                }),
                () -> store().transaction(ctx -> {
                    crdt.invoke("getValue");
                    return Option.apply(0);
                })
        });
    }
}
