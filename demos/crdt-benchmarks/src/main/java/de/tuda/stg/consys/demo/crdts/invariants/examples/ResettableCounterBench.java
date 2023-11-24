package de.tuda.stg.consys.demo.crdts.invariants.examples;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.crdts.CRDTBenchRunnable;
import de.tuda.stg.consys.invariants.lib.examples.resettablecounter.ResettableCounter;
import scala.Option;

import java.util.Random;

public class ResettableCounterBench extends CRDTBenchRunnable<ResettableCounter> {

	public static void main(String[] args) {
		JBenchExecution.execute("invariants-resettable-counter", ResettableCounterBench.class, args);
	}

	public ResettableCounterBench(JBenchStore adapter, BenchmarkConfig config) {
		super(adapter, config, ResettableCounter.class);
	}


	@Override
	@SuppressWarnings("consistency")
	public BenchmarkOperations operations() {
		final Random rand = new Random();

		return BenchmarkOperations.withUniformDistribution(new Runnable[] {
				() -> store().transaction(ctx -> {
					crdt.invoke("getValue");
					return Option.apply(0);
				}),
				() -> store().transaction(ctx -> {
					crdt.invoke("inc");
					return Option.apply(0);
				}),
				() -> store().transaction(ctx -> {
					crdt.invoke("reset");
					return Option.apply(0);
				})
		});
	}


}
