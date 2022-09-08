package de.tuda.stg.consys.demo.crdts;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.crdts.schema.LWWRegister;
import scala.Option;

import java.util.Random;

public class LWWRegisterRunnable extends CRDTBenchRunnable<LWWRegister> {
    public static void main(String[] args) {
        JBenchExecution.execute("crdt-lwwregister", GSetRunnable.class, args);
    }

    public LWWRegisterRunnable(JBenchStore adapter, BenchmarkConfig config) {
        super(adapter, config, LWWRegister.class);
    }

    private Random random = new Random();

    @Override
    @SuppressWarnings("consistency")
    public BenchmarkOperations operations() {
        return BenchmarkOperations.withUniformDistribution(new Runnable[] {
                () -> store().transaction(ctx -> {
                    crdt.invoke("set", random.nextInt(42), random.nextInt(42));
                    return Option.apply(0);
                }),
                () -> store().transaction(ctx -> {
                    crdt.invoke("get", random.nextInt(42));
                    return Option.apply(0);
                })
        });
    }
}
