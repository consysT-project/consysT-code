package de.tuda.stg.consys.demo.counter;

import com.typesafe.config.Config;
import de.tuda.stg.consys.bench.Benchmark;
import de.tuda.stg.consys.demo.counter.schema.Counter;
import de.tuda.stg.consys.objects.ConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JConsistencyLevels;
import de.tuda.stg.consys.objects.japi.JRef;
import org.checkerframework.com.google.common.collect.Sets;

/**
 * Created on 10.10.19.
 *
 * @author Mirko Köhler
 */
public class DistributedBenchmark extends Benchmark {


	public static void main(String[] args) {
		Benchmark.start(DistributedBenchmark.class, args[0]);
	}

	private static final int NUM_OF_TRANSACTIONS = 100;

	public DistributedBenchmark(String configName) {
		super(configName);
	}

	public DistributedBenchmark(Config config) {
		super(config);
	}

	private JRef<Counter> counter;
	private ConsistencyLevel level = JConsistencyLevels.STRONG;

	@Override
	public void setup() {
		if (processId() == 0) {
			counter = replicaSystem().replicate("counter", new Counter(0), level);
		} else {
			counter = replicaSystem().lookup("counter", Counter.class, level);
		}
	}

	@Override
	public void iteration() {
		for (int i = 0; i < NUM_OF_TRANSACTIONS; i++) {
			counter.ref().inc();
			System.out.print(i % 100 == 0 ? i : ".");
		}
		System.out.println();
	}

	@Override
	public void cleanup() {
		replicaSystem().clear(Sets.newHashSet());
	}


}
