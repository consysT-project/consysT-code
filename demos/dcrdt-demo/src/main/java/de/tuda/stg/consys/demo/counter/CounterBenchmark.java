package de.tuda.stg.consys.demo.counter;

import com.typesafe.config.Config;
import de.tuda.stg.consys.demo.DemoBenchmark;
import de.tuda.stg.consys.demo.counter.schema.AddOnlySet;
import de.tuda.stg.consys.japi.JConsistencyLevels;
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

	private JRef<AddOnlySet<String>> set;

	@Override
	public void setup() {

		if (processId() == 0) {
			set = system().replicate("counter", new AddOnlySet<String>(), JConsistencyLevels.DCRDT);
		} else {
			set = system().<AddOnlySet<String>>lookup("counter", (Class<AddOnlySet<String>>) new AddOnlySet<String>().getClass(), JConsistencyLevels.DCRDT);
			set.sync(); //Force dereference
		}
	}

	@Override
	public void operation() {
		set.ref().addElement("Hello");
		doSync(() -> set.sync());
		System.out.print(".");
	}

	@Override
	public void cleanup() {
		system().clear(Sets.newHashSet());
	}


}
