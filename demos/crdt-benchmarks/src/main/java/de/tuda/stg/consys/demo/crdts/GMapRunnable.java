package de.tuda.stg.consys.demo.crdts;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.crdts.schema.GMap;
import scala.Option;

import java.util.Random;

public class GMapRunnable extends CRDTBenchRunnable<GMap> {
    public static void main(String[] args) {
        JBenchExecution.execute("crdt-gmap", GSetRunnable.class, args);
    }

    public GMapRunnable(JBenchStore adapter, BenchmarkConfig config) {
        super(adapter, config, GMap.class);
    }

    private Random random = new Random();

    @Override
    @SuppressWarnings("consistency")
    public BenchmarkOperations operations() {
        return BenchmarkOperations.withUniformDistribution(new Runnable[] {
                () -> store().transaction(ctx -> {
                    crdt.invoke("put", random.nextInt(42), random.nextInt(42));
                    return Option.apply(0);
                }),
                () -> store().transaction(ctx -> {
                    crdt.invoke("containsKey", random.nextInt(42));
                    return Option.apply(0);
                }),
                () -> store().transaction(ctx -> {
                    crdt.invoke("containsValue", random.nextInt(42));
                    return Option.apply(0);
                }),
                () -> store().transaction(ctx -> {
                    crdt.invoke("isEmpty");
                    return Option.apply(0);
                }),
                () -> store().transaction(ctx -> {
                    crdt.invoke("get", random.nextInt(42));
                    return Option.apply(0);
                }),
                () -> store().transaction(ctx -> {
                    crdt.invoke("size");
                    return Option.apply(0);
                })
        });
    }
}
