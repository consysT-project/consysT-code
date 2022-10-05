package de.tuda.stg.consys.demo.counter;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchRunnable;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.counter.schema.Counter;
import de.tuda.stg.consys.japi.Ref;
import scala.Option;

/**
 * Created on 10.10.19.
 *
 * @author Mirko Köhler
 */
@SuppressWarnings({"consistency"})
public class CounterBenchmark extends JBenchRunnable {
	public static void main(String[] args) {
		JBenchExecution.execute("counter", CounterBenchmark.class, args);
	}

	public CounterBenchmark(JBenchStore adapter, BenchmarkConfig config) {
		super(adapter, config);
	}

	private Ref<Counter> counter;

	@Override
	public void setup() {
		if (processId() == 0) {
			counter = (Ref<@Mutable Counter>) store().<Ref<@Mutable Counter>>transaction(ctx -> Option.apply(
					ctx.replicate("counter", getLevel(), Counter.class, 0)
			)).get();
		}
		barrier("counter_added");
		if (processId() != 0) {
			counter = (Ref<@Mutable Counter>) store().<Ref<@Mutable Counter>>transaction(ctx -> Option.apply(
					ctx.lookup("counter", getLevel(), Counter.class)
			)).get();
		}
	}

	@Override
	public BenchmarkOperations operations() {
		return BenchmarkOperations.withUniformDistribution(new Runnable[] {
				() -> store().transaction(ctx -> {
					counter.ref().inc();
					return Option.apply(0);
				}),
				() -> store().transaction(ctx -> {
					counter.ref().get();
					return Option.apply(0);
				})
		});
	}

	@Override
	public void cleanup() {}

	private ConsistencyLevel getLevel() {
		switch (benchType()) {
			case WEAK: return getWeakLevel();
			case OP_MIXED: return getMixedLevel();
			case MIXED:
			case STRONG: return getStrongLevel();
			default: throw new UnsupportedOperationException("unknown bench type: " + benchType());
		}
	}
}
