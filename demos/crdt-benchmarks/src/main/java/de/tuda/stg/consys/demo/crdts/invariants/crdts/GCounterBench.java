package de.tuda.stg.consys.demo.crdts.invariants.crdts;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.crdts.CRDTBenchRunnable;
import de.tuda.stg.consys.demo.crdts.GCounterRunnable;
import de.tuda.stg.consys.invariants.lib.crdts.GCounter;
import scala.Option;

public class GCounterBench extends CRDTBenchRunnable<GCounter> {

	public static void main(String[] args) {
		JBenchExecution.execute("invariants-gcounter", GCounterBench.class, args);
	}

	public GCounterBench(JBenchStore adapter, BenchmarkConfig config) {
		super(adapter, config, GCounter.class);
	}

	@Override
	@SuppressWarnings("consistency")
	public BenchmarkOperations operations() {
		// One operation will be chosen randomly.
		return BenchmarkOperations.withUniformDistribution(new Runnable[] {
				// Here, operations are chosen with a uniform distribution.
				// The first operation increments the counter
				() -> store().transaction(ctx -> {
					crdt.invoke("inc");
					return Option.apply(0);
				}),
				// The second operation retrieves the value of the counter.
				() -> store().transaction(ctx -> {
					crdt.invoke("getValue");
					return Option.apply(0);
				})
		});
	}


}
