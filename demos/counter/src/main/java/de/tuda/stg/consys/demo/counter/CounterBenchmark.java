package de.tuda.stg.consys.demo.counter;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.demo.DemoRunnable;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.counter.schema.Counter;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.Store;
import de.tuda.stg.consys.japi.TransactionContext;
import scala.Option;

import java.io.Serializable;

/**
 * Created on 10.10.19.
 *
 * @author Mirko Köhler
 */
@SuppressWarnings({"consistency"})
public class CounterBenchmark<SStore extends de.tuda.stg.consys.core.store.Store>
		extends DemoRunnable<String, Serializable, TransactionContext<String, Serializable, ConsistencyLevel<SStore>>, Store<String, Serializable, ConsistencyLevel<SStore>, TransactionContext<String, Serializable, ConsistencyLevel<SStore>>>, SStore> {
	public static void main(String[] args) {
		JBenchExecution.execute("counter", CounterBenchmark.class, args);
	}

	public CounterBenchmark(
			JBenchStore<String, Serializable, TransactionContext<String, Serializable, ConsistencyLevel<SStore>>, Store<String, Serializable,
					ConsistencyLevel<SStore>,
					TransactionContext<String, Serializable, ConsistencyLevel<SStore>>>, SStore
					> adapter,
			BenchmarkConfig config) {
		super(adapter, config);

		switch (benchType) {
			case STRONG_DATACENTRIC:
			case WEAK_DATACENTRIC:
				throw new IllegalArgumentException("STRONG_DATACENTRIC, WEAK_DATACENTRIC not supported by counter bench");
		}
	}

	private Ref<Counter> counter;

	@Override
	public void setup() {
		if (processId() == 0) {
			counter = (Ref<@Mutable Counter>) store().<Ref<@Mutable Counter>>transaction(ctx -> Option.apply(
					ctx.replicate("counter", getLevelWithMixedFallback(getStrongLevel()), Counter.class, 0)
			)).get();
		}
		barrier("counter_added");
		if (processId() != 0) {
			counter = (Ref<@Mutable Counter>) store().<Ref<@Mutable Counter>>transaction(ctx -> Option.apply(
					ctx.lookup("counter", getLevelWithMixedFallback(getStrongLevel()), Counter.class)
			)).get();
		}
	}

	@Override
	public BenchmarkOperations operations() {
		return BenchmarkOperations.withUniformDistribution(new Runnable[] {
				() -> {
					Option<Integer> prevCount = store().transaction(ctx -> {
						int value = isTestMode ? counter.ref().get() : -1;

						counter.ref().inc();

						return Option.apply(value);
					});

					if (isTestMode) {
						store().transaction(ctx -> {
							check("counter was incremented", prevCount.get() < counter.ref().get());
							return Option.apply(0);
						});
					}
				},

				() -> store().transaction(ctx -> {
					counter.ref().get();
					return Option.apply(0);
				})
		});
	}

	@Override
	public void cleanup() {}

	@Override
	public void test() {
		if (processId() == 0) printTestResult();
	}
}
