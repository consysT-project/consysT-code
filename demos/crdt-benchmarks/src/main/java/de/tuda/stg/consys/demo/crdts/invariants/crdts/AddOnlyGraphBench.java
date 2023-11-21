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

	@SuppressWarnings("consistency")
	private @Immutable @Local List<@Immutable @Local Integer> vertices = IntStream.range(1, 100)
			.boxed()
      		.collect(Collectors.toCollection(ArrayList::new));

	private @Immutable @Local Integer getRandomVertex() {
		return vertices.get(new Random().nextInt(99));
	}

	@Override
	@SuppressWarnings("consistency")
	public BenchmarkOperations operations() {
		final Integer v1 = getRandomVertex();
		final Integer v2 = getRandomVertex();

		// One operation will be chosen randomly.
		return BenchmarkOperations.withUniformDistribution(new Runnable[] {
				// Here, operations are chosen with a uniform distribution.
				// The first operation increments the counter
				() -> store().transaction(ctx -> {
					crdt.invoke("hasVertex", v1);
					return Option.apply(0);
				}),
				// The second operation retrieves the value of the counter.
				() -> store().transaction(ctx -> {
					crdt.invoke("addVertex", v1);
					return Option.apply(0);
				}),
				() -> store().transaction(ctx -> {
					try {
						crdt.invoke("addEdge", v1, v2);
					} catch (IllegalArgumentException e) {

					}
					return Option.apply(0);
				})
		});
	}


}
