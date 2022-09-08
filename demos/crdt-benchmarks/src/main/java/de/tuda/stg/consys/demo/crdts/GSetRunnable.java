package de.tuda.stg.consys.demo.crdts;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.crdts.schema.GSet;
import scala.Option;

import java.util.Random;

public class GSetRunnable extends CRDTBenchRunnable<GSet> {

    public static void main(String[] args) {
        JBenchExecution.execute("crdt-gset", GSetRunnable.class, args);
    }

    public GSetRunnable(JBenchStore adapter, BenchmarkConfig config) {
        super(adapter, config, GSet.class);
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
                    crdt.invoke("contains", random.nextInt(42));
                    return Option.apply(0);
                })
        });
    }
}
