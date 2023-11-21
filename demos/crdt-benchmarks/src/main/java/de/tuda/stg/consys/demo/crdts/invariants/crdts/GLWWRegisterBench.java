package de.tuda.stg.consys.demo.crdts.invariants.crdts;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.crdts.CRDTBenchRunnable;
import de.tuda.stg.consys.invariants.lib.crdts.GSet;
import de.tuda.stg.consys.invariants.lib.crdts.LWWRegister;
import scala.Option;

import java.util.Random;

public class GLWWRegisterBench extends CRDTBenchRunnable<LWWRegister> {

	public static void main(String[] args) {
		JBenchExecution.execute("invariants-lww-register", GLWWRegisterBench.class, args);
	}

	public GLWWRegisterBench(JBenchStore adapter, BenchmarkConfig config) {
		super(adapter, config, LWWRegister.class);
	}


	@Override
	@SuppressWarnings("consistency")
	public BenchmarkOperations operations() {
		final Integer value = new Random().nextInt(100);

		return BenchmarkOperations.withUniformDistribution(new Runnable[] {
				() -> store().transaction(ctx -> {
					crdt.invoke("set", value);
					return Option.apply(0);
				}),
				() -> store().transaction(ctx -> {
					crdt.invoke("get");
					return Option.apply(0);
				})
		});
	}


}
