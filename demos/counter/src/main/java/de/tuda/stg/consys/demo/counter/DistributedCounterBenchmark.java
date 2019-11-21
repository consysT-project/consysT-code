package de.tuda.stg.consys.demo.counter;

import com.typesafe.config.Config;
import de.tuda.stg.consys.bench.DistributedBenchmark;
import de.tuda.stg.consys.demo.DemoBenchmark;
import de.tuda.stg.consys.demo.DemoUtils;
import de.tuda.stg.consys.demo.counter.schema.Counter;
import de.tuda.stg.consys.objects.japi.JRef;
import org.checkerframework.com.google.common.collect.Sets;

/**
 * Created on 10.10.19.
 *
 * @author Mirko Köhler
 */
public class DistributedCounterBenchmark extends DemoBenchmark {


	public static void main(String[] args) {
		start(DistributedCounterBenchmark.class, args[0]);
	}

	private final int numOfTransactions;


	public DistributedCounterBenchmark(Config config) {
		super(config);
		numOfTransactions = config.getInt("consys.bench.demo.counter.transactions");
	}

	private JRef<Counter> counter;

	@Override
	public void setup() {
		if (processId() == 0) {
			counter = replicaSystem().replicate("counter", new Counter(0), getCausalLevel());
		} else {
			counter = replicaSystem().lookup("counter", Counter.class, getCausalLevel());
			counter.sync(); //Force dereference
		}
	}

	@Override
	public void iteration() {
		if (processId() != 0) {
			for (int i = 0; i < numOfTransactions; i++) {
				counter.ref().inc();
				counter.sync();
				DemoUtils.printProgress(i);
			}
			DemoUtils.printDone();
		}
	}

	@Override
	public void cleanup() {
		replicaSystem().clear(Sets.newHashSet());
	}


}
