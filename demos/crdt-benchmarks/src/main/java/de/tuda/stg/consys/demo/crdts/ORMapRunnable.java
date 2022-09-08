package de.tuda.stg.consys.demo.crdts;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.crdts.schema.ORMap;
import scala.Option;

import java.util.Random;

public class ORMapRunnable extends CRDTBenchRunnable<ORMap> {
    public static void main(String[] args) {
        JBenchExecution.execute("crdt-ormap", GSetRunnable.class, args);
    }

    public ORMapRunnable(JBenchStore adapter, BenchmarkConfig config) {
        super(adapter, config, ORMap.class);
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
                    crdt.invoke("isEmpty");
                    return Option.apply(0);
                }),
                () -> store().transaction(ctx -> {
                    crdt.invoke("get", random.nextInt(42));
                    return Option.apply(0);
                }),
                () -> store().transaction(ctx -> {
                    crdt.invoke("remove", random.nextInt(42));
                    return Option.apply(0);
                })
        });
    }
}
