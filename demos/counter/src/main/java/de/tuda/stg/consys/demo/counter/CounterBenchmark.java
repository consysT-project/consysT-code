package de.tuda.stg.consys.demo.counter;

import com.typesafe.config.Config;
import de.tuda.stg.consys.bench.OutputFileResolver;
import de.tuda.stg.consys.demo.DemoBenchmark;
import de.tuda.stg.consys.demo.counter.schema.Counter;
import de.tuda.stg.consys.japi.legacy.JRef;
import org.checkerframework.com.google.common.collect.Sets;
import scala.Option;

/**
 * Created on 10.10.19.
 *
 * @author Mirko Köhler
 */
public class CounterBenchmark extends DemoBenchmark {
	public static void main(String[] args) {
		start(CounterBenchmark.class, args);
	}

	public CounterBenchmark(Config config, Option<OutputFileResolver> outputResolver) {
		super(config, outputResolver);
	}

	private JRef<Counter> counter;

	@Override
	public void setup() {
		if (processId() == 0) {
			counter = system().replicate("counter", new Counter(0), getWeakLevel());
		} else {
			counter = system().lookup("counter", Counter.class, getWeakLevel());
			counter.sync(); //Force dereference
		}
	}

	@Override
	public void operation() {
		counter.ref().inc();
		doSync(() -> counter.sync());
		System.out.print(".");
	}

	@Override
	public void cleanup() {
		system().clear(Sets.newHashSet());
	}


}
