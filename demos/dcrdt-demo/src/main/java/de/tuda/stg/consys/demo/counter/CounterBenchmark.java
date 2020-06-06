package de.tuda.stg.consys.demo.counter;

import com.typesafe.config.Config;
import de.tuda.stg.consys.demo.DemoBenchmark;
import de.tuda.stg.consys.demo.counter.schema.AddOnlySet;
import de.tuda.stg.consys.japi.JRef;
import org.checkerframework.com.google.common.collect.Sets;

/**
 * Created on 10.10.19.
 *
 * @author Mirko Köhler
 */
public class CounterBenchmark extends DemoBenchmark {
	public static void main(String[] args) {
		start(CounterBenchmark.class, args[0]);
	}

	public CounterBenchmark(Config config) {
		super(config);
	}

	private JRef<AddOnlySet> counter;

	@Override
	public void setup() {

		if (processId() == 0) {
			counter = system().replicate("counter", new AddOnlySet(0), getWeakLevel());
		} else {
			counter = system().lookup("counter", AddOnlySet.class, getWeakLevel());
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
