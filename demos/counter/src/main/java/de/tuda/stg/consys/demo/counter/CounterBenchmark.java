package de.tuda.stg.consys.demo.counter;

import com.typesafe.config.Config;
import de.tuda.stg.consys.bench.OutputFileResolver;
import de.tuda.stg.consys.demo.CassandraDemoBenchmark;
import de.tuda.stg.consys.demo.counter.schema.Counter;
import de.tuda.stg.consys.japi.Ref;
import scala.Option;

/**
 * Created on 10.10.19.
 *
 * @author Mirko Köhler
 */
public class CounterBenchmark extends CassandraDemoBenchmark {
	public static void main(String[] args) {
		start(CounterBenchmark.class, args);
	}

	public CounterBenchmark(Config config, Option<OutputFileResolver> outputResolver) {
		super(config, outputResolver);
	}

	private Ref<Counter> counter;

	@Override
	public void setup() {
		if (processId() == 0) {
			counter = store().transaction(ctx -> Option.apply(ctx.replicate("counter", getWeakLevel(), Counter.class, 0))).get();
		} else {
			counter = store().transaction(ctx -> Option.apply(ctx.lookup("counter", getWeakLevel(), Counter.class))).get();
		}
	}

	@Override
	public void operation() {
		store().transaction(ctx -> {
			counter.ref().inc();
			return Option.empty();
		});
		System.out.print(".");
	}

	@Override
	public void cleanup() {
		//system().clear(Sets.newHashSet());
	}
}
