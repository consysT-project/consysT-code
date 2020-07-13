package de.tuda.stg.consys.demo.dcrdt;

import com.typesafe.config.Config;
import de.tuda.stg.consys.demo.DemoBenchmark;
import de.tuda.stg.consys.demo.dcrdt.schema.AddOnlySetString;
import de.tuda.stg.consys.demo.dcrdt.schema.DotStoreString;
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

	private JRef<AddOnlySetString> set;

	@Override
	public void setup() {
		System.out.println("setup");

		if (processId() == 0) {
			set = system().replicate("counter", new AddOnlySetString(), JConsistencyLevels.DCRDT);
		} else {
			set = system().<AddOnlySetString>lookup("counter", AddOnlySetString.class, JConsistencyLevels.DCRDT);
			set.sync(); //Force dereference
		}
		System.out.println(processId() + " finished setup");
	}

	@Override
	public void operation() {
		set.ref().addElement("Hello from "+processId());
		//set.ref().addString("Hello from "+ processId(), processId());
		//set.ref().removeString("Hello from "+ processId(),processId());
		//String s = set.ref().toString() + "i am "+ processId();
		//System.out.println(s);
		//set.ref().addString("Hello from "+ processId(), processId());

		doSync(() -> set.sync());
		System.out.print(".");
	}

	@Override
	public void cleanup() {
		system().clear(Sets.newHashSet());
	}


}
