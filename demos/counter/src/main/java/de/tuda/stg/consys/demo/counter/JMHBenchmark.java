package de.tuda.stg.consys.demo.counter;

import de.tuda.stg.consys.core.legacy.ConsistencyLabel;
import de.tuda.stg.consys.demo.counter.schema.Counter;
import de.tuda.stg.consys.japi.legacy.JConsistencyLevels;
import de.tuda.stg.consys.japi.legacy.JRef;
import de.tuda.stg.consys.japi.legacy.JReplicaSystem;
import de.tuda.stg.consys.japi.legacy.impl.JReplicaSystems;
import org.openjdk.jmh.Main;
import org.openjdk.jmh.annotations.*;

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

		JReplicaSystem replicaSystem1;
		JReplicaSystem replicaSystem2;
		JReplicaSystem replicaSystem3;

		List<JRef<Counter>> counters;

		public List<JRef<Counter>> getCounters() {
			return counters;
		}

		int index;

		public int getIndex() {
			return index;
		}

		@Setup(Level.Iteration)
		public void systemSetup() throws Exception {

			JReplicaSystem[] systems = JReplicaSystems.fromActorSystemForTesting(3);

			replicaSystem1 = systems[0];
			replicaSystem2 = systems[1];
			replicaSystem3 = systems[2];

			ConsistencyLabel consistencyLevel = level.equals("weak") ? JConsistencyLevels.WEAK : JConsistencyLevels.STRONG;

			replicaSystem1.replicate("counter1", new Counter(0), consistencyLevel);
			replicaSystem2.replicate("counter2", new Counter(0), consistencyLevel);
			replicaSystem3.replicate("counter3", new Counter(0), consistencyLevel);

			counters = new ArrayList<>();
			counters.add(replicaSystem1.lookup("counter1", Counter.class, consistencyLevel));
			counters.add(replicaSystem1.lookup("counter2", Counter.class, consistencyLevel));
			counters.add(replicaSystem1.lookup("counter3", Counter.class, consistencyLevel));
			counters.add(replicaSystem2.lookup("counter1", Counter.class, consistencyLevel));
			counters.add(replicaSystem2.lookup("counter2", Counter.class, consistencyLevel));
			counters.add(replicaSystem2.lookup("counter3", Counter.class, consistencyLevel));
			counters.add(replicaSystem3.lookup("counter1", Counter.class, consistencyLevel));
			counters.add(replicaSystem3.lookup("counter2", Counter.class, consistencyLevel));
			counters.add(replicaSystem3.lookup("counter3", Counter.class, consistencyLevel));

			index = -1;

			Thread.sleep(1000);
		}

		@TearDown(Level.Iteration)
		public void systemTeardown() throws Exception {
			replicaSystem1.close();
			replicaSystem2.close();
			replicaSystem3.close();
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
