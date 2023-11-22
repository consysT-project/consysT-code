package de.tuda.stg.consys.demo.crdts.invariants.crdts;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.checker.qual.Immutable;
import de.tuda.stg.consys.checker.qual.Local;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.crdts.CRDTBenchRunnable;
import de.tuda.stg.consys.invariants.lib.crdts.AddOnlyGraph;
import de.tuda.stg.consys.invariants.lib.crdts.GCounter;
import scala.Option;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

public class AddOnlyGraphBench extends CRDTBenchRunnable<AddOnlyGraph> {

	public static void main(String[] args) {
		JBenchExecution.execute("invariants-add-only-graph", AddOnlyGraphBench.class, args);
	}

	public AddOnlyGraphBench(JBenchStore adapter, BenchmarkConfig config) {
		super(adapter, config, AddOnlyGraph.class);
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
					crdt.invoke("hasVertex", rand.nextInt(99));
					return Option.apply(0);
				}),
				// The second operation retrieves the value of the counter.
				() -> store().transaction(ctx -> {
					crdt.invoke("addVertex", rand.nextInt(99));
					return Option.apply(0);
				}),
				() -> store().transaction(ctx -> {
					try {
						crdt.invoke("addEdge", rand.nextInt(99), rand.nextInt(99));
					} catch (IllegalArgumentException e) {

					}
					return Option.apply(0);
				})
		});
	}


}
