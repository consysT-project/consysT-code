package de.tuda.stg.consys.demo.crdts.invariants.crdts;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.crdts.CRDTBenchRunnable;
import de.tuda.stg.consys.invariants.lib.crdts.LWWRegister;
import scala.Option;

import java.util.Random;

public class LWWRegisterBench extends CRDTBenchRunnable<LWWRegister> {

	public static void main(String[] args) {
		JBenchExecution.execute("invariants-lww-register", LWWRegisterBench.class, args);
	}

	public LWWRegisterBench(JBenchStore adapter, BenchmarkConfig config) {
		super(adapter, config, LWWRegister.class);
	}


	@Override
	@SuppressWarnings("consistency")
	public BenchmarkOperations operations() {
		final Random rand = new Random();

		return BenchmarkOperations.withUniformDistribution(new Runnable[] {
				() -> store().transaction(ctx -> {
					crdt.invoke("set", rand.nextInt(99));
					return Option.apply(0);
				}),
				() -> store().transaction(ctx -> {
					crdt.invoke("get");
					return Option.apply(0);
				})
		});
	}


}
