package de.tuda.stg.consys.demo.dcrdt;

import com.typesafe.config.Config;
import de.tuda.stg.consys.demo.DemoBenchmark;
import de.tuda.stg.consys.demo.dcrdt.schema.AddOnlySetString;
import de.tuda.stg.consys.demo.dcrdt.schema.Hashmap;
import de.tuda.stg.consys.demo.dcrdt.schema.StringHashmap;
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

	private JRef<StringHashmap> map;

	@Override
	public void setup() {
		System.out.println("setup");

		if (processId() == 0) {
			map = system().replicate("counter", new StringHashmap(), JConsistencyLevels.DCRDT);
		} else {
			map = system().<StringHashmap>lookup("counter", StringHashmap.class, JConsistencyLevels.DCRDT);
			map.sync(); //Force dereference
		}
		System.out.println(processId() + " finished setup");
	}

	@Override
	public void operation() {

		map.ref().addEntry("Key " + processId(), "Value " + processId());

		doSync(() -> map.sync());
		System.out.print(".");
	}

	@Override
	public void cleanup() {
		system().clear(Sets.newHashSet());
	}


}
