package de.tuda.stg.consys.demo.crdts.invariants.examples;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.crdts.CRDTBenchRunnable;
import de.tuda.stg.consys.invariants.lib.examples.bankaccountlww.BankAccountLWW;
import de.tuda.stg.consys.invariants.lib.examples.consensus.Consensus;
import scala.Option;

import java.util.Random;

public class ConsensusBench extends CRDTBenchRunnable<Consensus> {

	public static void main(String[] args) {
		JBenchExecution.execute("invariants-consensus", ConsensusBench.class, args);
	}

	public ConsensusBench(JBenchStore adapter, BenchmarkConfig config) {
		super(adapter, config, Consensus.class);
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
					try {
						crdt.invoke("agree");
					} catch (RuntimeException e) {

					}
					return Option.apply(0);
				}),
				// The second operation retrieves the value of the counter.
				() -> store().transaction(ctx -> {
					crdt.invoke("mark");
					return Option.apply(0);
				}),
				() -> store().transaction(ctx -> {
					try {
						crdt.invoke("conjunctValues");
					} catch (IllegalArgumentException e) {

					}
					return Option.apply(0);
				})
		});
	}


}
