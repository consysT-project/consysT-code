package de.tuda.stg.consys.demo.crdts.invariants.crdts;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.crdts.CRDTBenchRunnable;
import de.tuda.stg.consys.invariants.lib.crdts.AddOnlyGraph;
import de.tuda.stg.consys.invariants.lib.crdts.BoundedCounter;
import scala.Option;

import java.util.Random;

public class BoundedCounterBench extends CRDTBenchRunnable<BoundedCounter> {

	public static void main(String[] args) {
		JBenchExecution.execute("invariants-bounded-counter", BoundedCounterBench.class, args);
	}

	public BoundedCounterBench(JBenchStore adapter, BenchmarkConfig config) {
		super(adapter, config, BoundedCounter.class);
	}


	@Override
	@SuppressWarnings("consistency")
	public BenchmarkOperations operations() {
		final Random rand = new Random();

		// One operation will be chosen randomly.
		return BenchmarkOperations.withUniformDistribution(new Runnable[] {
				// Here, operations are chosen with a uniform distribution.
				// The first operation increments the counter
				() -> store().transaction(ctx -> {
					crdt.invoke("increment", rand.nextInt(99));
					return Option.apply(0);
				}),
				() -> store().transaction(ctx -> {
					crdt.invoke("getValue");
					return Option.apply(0);
				}),
				() -> store().transaction(ctx -> {
					crdt.invoke("getQuota");
					return Option.apply(0);
				}),
				// The second operation retrieves the value of the counter.
				() -> store().transaction(ctx -> {
					try {
						crdt.invoke("decrement", rand.nextInt(99));
					} catch (IllegalArgumentException e) {

					}
					return Option.apply(0);
				}),
				() -> store().transaction(ctx -> {
					try {
						crdt.invoke("transfer", rand.nextInt(numOfProcesses()), rand.nextInt(99));
					} catch (IllegalArgumentException e) {

					}
					return Option.apply(0);
				})
		});
	}


}
