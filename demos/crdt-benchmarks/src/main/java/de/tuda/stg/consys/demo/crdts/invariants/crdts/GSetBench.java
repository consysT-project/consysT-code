package de.tuda.stg.consys.demo.crdts.invariants.crdts;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.checker.qual.Immutable;
import de.tuda.stg.consys.checker.qual.Local;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.crdts.CRDTBenchRunnable;
import de.tuda.stg.consys.invariants.lib.crdts.GCounter;
import de.tuda.stg.consys.invariants.lib.crdts.GMap;
import de.tuda.stg.consys.invariants.lib.crdts.GSet;
import scala.Option;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

public class GSetBench extends CRDTBenchRunnable<GSet> {

	public static void main(String[] args) {
		JBenchExecution.execute("invariants-gset", GSetBench.class, args);
	}

	public GSetBench(JBenchStore adapter, BenchmarkConfig config) {
		super(adapter, config, GSet.class);
	}


	@Override
	@SuppressWarnings("consistency")
	public BenchmarkOperations operations() {
		final Random rand = new Random();

		return BenchmarkOperations.withUniformDistribution(new Runnable[] {
				() -> store().transaction(ctx -> {
					crdt.invoke("add", rand.nextInt(99));
					return Option.apply(0);
				}),
				() -> store().transaction(ctx -> {
					crdt.invoke("contains", rand.nextInt(99));
					return Option.apply(0);
				}),
				() -> store().transaction(ctx -> {
					crdt.invoke("isEmpty");
					return Option.apply(0);
				}),
				() -> store().transaction(ctx -> {
					crdt.invoke("getValue");
					return Option.apply(0);
				})
		});
	}


}
