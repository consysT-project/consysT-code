package de.tuda.stg.consys.demo.crdts.invariants.examples;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.crdts.CRDTBenchRunnable;
import de.tuda.stg.consys.invariants.lib.examples.jointbankaccount.JointBankAccount;
import scala.Option;

import java.util.Random;

public class JointBankAccountBench extends CRDTBenchRunnable<JointBankAccount> {

	public static void main(String[] args) {
		JBenchExecution.execute("invariants-joint-bank-account", JointBankAccountBench.class, args);
	}

	public JointBankAccountBench(JBenchStore adapter, BenchmarkConfig config) {
		super(adapter, config, JointBankAccount.class);
	}


	@Override
	@SuppressWarnings("consistency")
	public BenchmarkOperations operations() {
		final Random rand = new Random();

		return BenchmarkOperations.withUniformDistribution(new Runnable[] {
				() -> store().transaction(ctx -> {
					crdt.invoke("request");
					return Option.apply(0);
				}),
				() -> store().transaction(ctx -> {
					crdt.invoke("approve");
					return Option.apply(0);
				}),
				() -> store().transaction(ctx -> {
					crdt.invoke("reset");
					return Option.apply(0);
				}),
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
