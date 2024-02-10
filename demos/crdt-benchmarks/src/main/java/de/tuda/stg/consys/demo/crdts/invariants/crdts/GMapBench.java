package de.tuda.stg.consys.demo.crdts.invariants.crdts;

import com.google.common.collect.Lists;
import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.checker.qual.Immutable;
import de.tuda.stg.consys.checker.qual.Local;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.crdts.CRDTBenchRunnable;
import de.tuda.stg.consys.invariants.lib.crdts.GCounter;
import de.tuda.stg.consys.invariants.lib.crdts.GMap;
import scala.Option;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

public class GMapBench extends CRDTBenchRunnable<GMap> {

	public static void main(String[] args) {
		JBenchExecution.execute("invariants-gmap", GMapBench.class, args);
	}

	public GMapBench(JBenchStore adapter, BenchmarkConfig config) {
		super(adapter, config, GMap.class);
	}

	@SuppressWarnings("consistency")
	private List<Integer> keys = IntStream.range(1, 100)
			.boxed()
			.collect(Collectors.toCollection(ArrayList::new));

	@Override
	@SuppressWarnings("consistency")
	public BenchmarkOperations operations() {
		final Random rand = new Random();

		return BenchmarkOperations.withUniformDistribution(new Runnable[] {
				() -> store().transaction(ctx -> {
					crdt.invoke("containsKey", keys.get(rand.nextInt(99)));
					return Option.apply(0);
				}),
				() -> store().transaction(ctx -> {
					crdt.invoke("containsValue", new GCounter());
					return Option.apply(0);
				}),
				() -> store().transaction(ctx -> {
					crdt.invoke("isEmpty");
					return Option.apply(0);
				}),
				() -> store().transaction(ctx -> {
					crdt.invoke("get", keys.get(rand.nextInt(99)));
					return Option.apply(0);
				}),
				() -> store().transaction(ctx -> {
					crdt.invoke("put", keys.get(rand.nextInt(99)), new GCounter());
					return Option.apply(0);
				}),
				() -> store().transaction(ctx -> {
					crdt.invoke("size");
					return Option.apply(0);
				})
		});
	}


}
