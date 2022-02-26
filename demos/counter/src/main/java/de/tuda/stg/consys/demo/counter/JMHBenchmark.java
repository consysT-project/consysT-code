package de.tuda.stg.consys.demo.counter;

import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.demo.counter.schema.Counter;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.Cassandra;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import org.openjdk.jmh.Main;
import org.openjdk.jmh.annotations.*;
import scala.Option;
import scala.concurrent.duration.Duration;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

@Warmup(iterations = 4)
@Measurement(iterations = 4)
@BenchmarkMode(Mode.SampleTime)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
@Fork(3)
public class JMHBenchmark {
	public static void main(String[] args) throws Exception {
		Main.main(args);
	}

	@State(Scope.Benchmark)
	public static class BenchmarkSetup {
		@Param({"weak", "local/strong"})
		String level;

		CassandraStoreBinding replica1;
		CassandraStoreBinding replica2;
		CassandraStoreBinding replica3;

		List<Ref<Counter>> counters;

		public List<Ref<Counter>> getCounters() {
			return counters;
		}

		int index;

		public int getIndex() {
			return index;
		}

		@Setup(Level.Iteration)
		public void systemSetup() throws Exception {

			CassandraStoreBinding[] systems = {
					Cassandra.newReplica("127.0.0.1", 9042, 2181,
							Duration.apply(50, "ms"), true),
					Cassandra.newReplica("127.0.0.2", 9042, 2181,
							Duration.apply(50, "ms"), false),
					Cassandra.newReplica("127.0.0.3", 9042, 2181,
							Duration.apply(50, "ms"), false),

			};

			replica1 = systems[0];
			replica2 = systems[1];
			replica3 = systems[2];

			ConsistencyLevel<CassandraStore> consistencyLevel = level.equals("weak") ?
					CassandraConsistencyLevels.WEAK : CassandraConsistencyLevels.STRONG;

			replica1.transaction(ctx -> Option.apply(
					ctx.replicate("counter1", consistencyLevel, Counter.class, 0)));
			replica2.transaction(ctx -> Option.apply(
					ctx.replicate("counter2", consistencyLevel, Counter.class, 0)));
			replica3.transaction(ctx -> Option.apply(
					ctx.replicate("counter3", consistencyLevel, Counter.class, 0)));

			counters = new ArrayList<>();
			counters.add(replica1.transaction(ctx -> Option.apply(
					ctx.lookup("counter1", consistencyLevel, Counter.class))).get());
			counters.add(replica1.transaction(ctx -> Option.apply(
					ctx.lookup("counter2", consistencyLevel, Counter.class))).get());
			counters.add(replica1.transaction(ctx -> Option.apply(
					ctx.lookup("counter3", consistencyLevel, Counter.class))).get());
			counters.add(replica2.transaction(ctx -> Option.apply(
					ctx.lookup("counter1", consistencyLevel, Counter.class))).get());
			counters.add(replica2.transaction(ctx -> Option.apply(
					ctx.lookup("counter2", consistencyLevel, Counter.class))).get());
			counters.add(replica2.transaction(ctx -> Option.apply(
					ctx.lookup("counter3", consistencyLevel, Counter.class))).get());
			counters.add(replica3.transaction(ctx -> Option.apply(
					ctx.lookup("counter1", consistencyLevel, Counter.class))).get());
			counters.add(replica3.transaction(ctx -> Option.apply(
					ctx.lookup("counter2", consistencyLevel, Counter.class))).get());
			counters.add(replica3.transaction(ctx -> Option.apply(
					ctx.lookup("counter3", consistencyLevel, Counter.class))).get());

			index = -1;

			Thread.sleep(1000);
		}

		@TearDown(Level.Iteration)
		public void systemTeardown() throws Exception {
			replica1.close();
			replica2.close();
			replica3.close();
		}

		@Setup(Level.Invocation)
		public void indexSetup() throws Exception {
			index = (index + 1) % counters.size();
		}
	}

	@Benchmark
	public void benchmark(BenchmarkSetup setup) {
		setup.getCounters().get(setup.getIndex()).invoke("inc");
	}
}
