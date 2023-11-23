package de.tuda.stg.consys.demo.crdts.invariants.examples;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.crdts.CRDTBenchRunnable;
import de.tuda.stg.consys.invariants.lib.examples.consensus.Consensus;
import de.tuda.stg.consys.invariants.lib.examples.distributedlock.DistributedLock;
import scala.Option;

import java.util.Random;

public class DistributedLockBench extends CRDTBenchRunnable<DistributedLock> {

	public static void main(String[] args) {
		JBenchExecution.execute("invariants-distributed-lock", DistributedLockBench.class, args);
	}

	public DistributedLockBench(JBenchStore adapter, BenchmarkConfig config) {
		super(adapter, config, DistributedLock.class);
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
					crdt.invoke("transfer", rand.nextInt(numOfProcesses()));
					return Option.apply(0);
				})
		});
	}


}
