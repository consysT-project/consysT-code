package de.tuda.stg.consys.demo.counter;

import com.typesafe.config.Config;
import com.typesafe.config.ConfigFactory;
import de.tuda.stg.consys.bench.DistBenchmark;
import de.tuda.stg.consys.demo.counter.schema.Counter;
import de.tuda.stg.consys.objects.ConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JConsistencyLevels;
import de.tuda.stg.consys.objects.japi.JRef;
import org.checkerframework.com.google.common.collect.Sets;

import java.io.File;

/**
 * Created on 10.10.19.
 *
 * @author Mirko Köhler
 */
public class DistributedBenchmark extends DistBenchmark {


	public static void main(String[] args) {
		Config config = ConfigFactory.parseFile(new File("./resources/" + args[0]));
		DistBenchmark bench = new DistributedBenchmark(config);
		bench.runBenchmark();
	}

	private static final int NUM_OF_TRANSACTIONS = 10000;

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
		if (processId == 0) {
			counter = replicaSystem.replicate("counter", new Counter(0), level);
		} else {
			counter = replicaSystem.lookup("counter", Counter.class, level);
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
	protected void cleanup() {
		replicaSystem.clear(Sets.newHashSet());
	}


}
