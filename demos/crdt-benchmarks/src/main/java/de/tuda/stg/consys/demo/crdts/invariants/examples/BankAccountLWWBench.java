package de.tuda.stg.consys.demo.crdts.invariants.examples;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.crdts.CRDTBenchRunnable;
import de.tuda.stg.consys.invariants.lib.examples.bankaccount.BankAccount;
import de.tuda.stg.consys.invariants.lib.examples.bankaccountlww.BankAccountLWW;
import scala.Option;

import java.util.Random;

public class BankAccountLWWBench extends CRDTBenchRunnable<BankAccountLWW> {

	public static void main(String[] args) {
		JBenchExecution.execute("invariants-bank-account-lww", BankAccountLWWBench.class, args);
	}

	public BankAccountLWWBench(JBenchStore adapter, BenchmarkConfig config) {
		super(adapter, config, BankAccountLWW.class);
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
					crdt.invoke("getValue");
					return Option.apply(0);
				}),
				// The second operation retrieves the value of the counter.
				() -> store().transaction(ctx -> {
					crdt.invoke("deposit", rand.nextInt(99));
					return Option.apply(0);
				}),
				() -> store().transaction(ctx -> {
					try {
						crdt.invoke("withdraw", rand.nextInt(99));
					} catch (IllegalArgumentException e) {

					}
					return Option.apply(0);
				})
		});
	}


}
