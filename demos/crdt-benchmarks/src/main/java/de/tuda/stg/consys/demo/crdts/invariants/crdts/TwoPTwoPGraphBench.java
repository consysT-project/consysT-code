package de.tuda.stg.consys.demo.crdts.invariants.crdts;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.crdts.CRDTBenchRunnable;
import de.tuda.stg.consys.invariants.lib.crdts.TwoPTwoPGraph;
import de.tuda.stg.consys.invariants.lib.crdts.TwoPhaseSet;
import scala.Option;

import java.util.Random;

public class TwoPTwoPGraphBench extends CRDTBenchRunnable<TwoPTwoPGraph> {
    public static void main(String[] args) {
        JBenchExecution.execute("invariants-twoptwopgraph", TwoPTwoPGraphBench.class, args);
    }

    public TwoPTwoPGraphBench(JBenchStore adapter, BenchmarkConfig config) {
        super(adapter, config, TwoPTwoPGraph.class);
    }

    private Random random = new Random();

    @Override
    @SuppressWarnings("consistency")
    public BenchmarkOperations operations() {
        return BenchmarkOperations.withUniformDistribution(new Runnable[] {
                () -> store().transaction(ctx -> {
                    crdt.invoke("addVertex", random.nextInt(99));
                    return Option.apply(0);
                }),
                () -> store().transaction(ctx -> {
                    try {
                        crdt.invoke("addEdge", random.nextInt(99), random.nextInt(99));
                    } catch (IllegalArgumentException e) {

                    }

                    return Option.apply(0);
                }),
                () -> store().transaction(ctx -> {
                    try {
                        crdt.invoke("removeVertex", random.nextInt(99));
                    } catch (IllegalArgumentException e) {

                    }
                    return Option.apply(0);
                }),
                () -> store().transaction(ctx -> {
                    crdt.invoke("removeEdge", random.nextInt(99), random.nextInt(99));
                    return Option.apply(0);
                }),
                () -> store().transaction(ctx -> {
                    crdt.invoke("hasVertex", random.nextInt(99));
                    return Option.apply(0);
                })
        });
    }
}
