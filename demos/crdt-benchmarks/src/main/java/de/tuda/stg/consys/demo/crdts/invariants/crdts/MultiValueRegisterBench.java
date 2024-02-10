package de.tuda.stg.consys.demo.crdts.invariants.crdts;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.crdts.CRDTBenchRunnable;
import de.tuda.stg.consys.invariants.lib.crdts.LWWRegister;
import de.tuda.stg.consys.invariants.lib.crdts.MultiValueRegister;
import scala.Option;

import java.util.Random;

public class MultiValueRegisterBench extends CRDTBenchRunnable<MultiValueRegister> {

	public static void main(String[] args) {
		JBenchExecution.execute("invariants-multi-value-register", MultiValueRegisterBench.class, args);
	}

	public MultiValueRegisterBench(JBenchStore adapter, BenchmarkConfig config) {
		super(adapter, config, MultiValueRegister.class);
	}


	@Override
	@SuppressWarnings("consistency")
	public BenchmarkOperations operations() {
		final Random rand = new Random();

		return BenchmarkOperations.withUniformDistribution(new Runnable[] {
				() -> store().transaction(ctx -> {
					crdt.invoke("write", rand.nextInt(99));
					return Option.apply(0);
				}),
				() -> store().transaction(ctx -> {
					crdt.invoke("read");
					return Option.apply(0);
				})
		});
	}


}
