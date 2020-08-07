package de.tuda.stg.consys.demo.dcrdt;

import com.typesafe.config.Config;
import de.tuda.stg.consys.core.Address;
import de.tuda.stg.consys.core.akka.VectorClock;
import de.tuda.stg.consys.demo.DemoBenchmark;
<<<<<<< HEAD
import de.tuda.stg.consys.demo.dcrdt.schema.AddOnlySetString;
import de.tuda.stg.consys.demo.dcrdt.schema.Hashmap;
import de.tuda.stg.consys.demo.dcrdt.schema.StringHashmap;
=======
import de.tuda.stg.consys.demo.dcrdt.schema.*;
>>>>>>> 02160a0b2053e5b64b23be342691dd274ccf3dc0
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

<<<<<<< HEAD
	private JRef<StringHashmap> map;
=======
	private JRef<DotStoreString> dotStore;

	private JRef<AddOnlySetString> set;
>>>>>>> 02160a0b2053e5b64b23be342691dd274ccf3dc0

	private JRef<AddOnlySetString> set2;

	private JRef<AddRemoveSet> addRemove;

	private JRef<IntegerVector> vector;

	private  JRef<DCRDTHashMap> hashMap;

	private int switcher = 4;

	@Override
	public void setup() {
	/*	System.out.println("setup");
		if (processId() == 0) {
<<<<<<< HEAD
			map = system().replicate("counter", new StringHashmap(), JConsistencyLevels.DCRDT);
		} else {
			map = system().<StringHashmap>lookup("counter", StringHashmap.class, JConsistencyLevels.DCRDT);
			map.sync(); //Force dereference
=======
			dotStore = system().replicate("counter", new DotStoreString(), JConsistencyLevels.DCRDT);
		} else {
			dotStore = system().lookup("counter", DotStoreString.class, JConsistencyLevels.DCRDT);
			dotStore.sync(); //Force dereference
>>>>>>> 02160a0b2053e5b64b23be342691dd274ccf3dc0
		}
		System.out.println(processId() + " finished setup of dotStore");
		*/

		switch (switcher) {
			case 0:
				if (processId() == 0) {
					dotStore = system().replicate("counter", new DotStoreString(), JConsistencyLevels.DCRDT);
				} else {
					dotStore = system().lookup("counter", DotStoreString.class, JConsistencyLevels.DCRDT);
					dotStore.sync(); //Force dereference
				}
				System.out.println(processId() + " finished setup of dotStore");
				break;

			case 1:
				if (processId() == 0) {
					set = system().replicate("counter", new AddOnlySetString(), JConsistencyLevels.DCRDT);
				} else {
					set = system().lookup("counter", AddOnlySetString.class, JConsistencyLevels.DCRDT);
					set.sync(); //Force dereference
				}
				System.out.println(processId() + " finished setup of set");
				break;

			case 2:
				if (processId() == 0) {
					addRemove = system().replicate("counter", new AddRemoveSet(), JConsistencyLevels.DCRDT);
				} else {
					addRemove = system().lookup("counter", AddRemoveSet.class, JConsistencyLevels.DCRDT);
					addRemove.sync(); //Force dereference
				}
				System.out.println(processId() + " finished setup of addRemove");
				break;

			case 3:
				if (processId() == 0) {
					vector = system().replicate("counter", new IntegerVector(5), JConsistencyLevels.DCRDT);
				} else {
					vector = system().lookup("counter", IntegerVector.class, JConsistencyLevels.DCRDT);
					vector.sync(); //Force dereference
				}
				System.out.println(processId() + " finished setup of vectorClock");
				break;

			case 4:
				if (processId() == 0) {
					hashMap = system().replicate("counter", new DCRDTHashMap(), JConsistencyLevels.DCRDT);
					set = system().replicate("counter2", new AddOnlySetString(), JConsistencyLevels.DCRDT);
					set2 = system().replicate("counter3", new AddOnlySetString(), JConsistencyLevels.DCRDT);

				} else {
					hashMap = system().lookup("counter", DCRDTHashMap.class, JConsistencyLevels.DCRDT);
					hashMap.sync(); //Force dereference
					set = system().lookup("counter2", AddOnlySetString.class, JConsistencyLevels.DCRDT);
					set.sync(); //Force dereference
					set2 = system().lookup("counter3", AddOnlySetString.class, JConsistencyLevels.DCRDT);
					set2.sync(); //Force dereference
				}
				System.out.println(processId() + " finished setup of HashMap");
				break;

		}

	}

	@Override
	public void operation() {
		/*dotStore.ref().addString("Hello from " + processId(), processId());
		dotStore.ref().removeString("Hello from " + processId(), processId());
		String s = dotStore.ref().toString() + "i am " + processId();
		System.out.println(s);
		doSync(() -> dotStore.sync());
		System.out.print(".");*/

		switch (switcher) {
			case 0:
				dotStore.ref().addString("Hello from " + processId(), processId());
				dotStore.ref().removeString("Hello from " + processId(), processId());
				String s = "current String of" + processId() +" after removal: "+dotStore.ref().toString();
				System.out.println(s);
				doSync(() -> dotStore.sync());
				System.out.print(".");
				break;
			case 1:
				set.ref().addElement("Hello from "+ processId() );
				doSync(() -> set.sync());
				System.out.print(".");
				break;

<<<<<<< HEAD
		map.ref().addEntry("Key " + processId(), "Value " + processId());

		doSync(() -> map.sync());
		System.out.print(".");
=======
			case 2:
				addRemove.ref().addElement("Hello from " + processId());
				addRemove.ref().removeElement("Hello from "+processId());
				addRemove.ref().addElement("Hello from " + processId());
				//Does not add this one because it is a Tombstone Set
				String x ="result: "+ addRemove.ref().toString();
				System.out.println(x);
				doSync(() -> addRemove.sync());
				System.out.print(".");
				break;

			case 3:
				vector.ref().inc(0);
				doSync(() -> vector.sync());
				System.out.print(".");
				break;

			case 4:
				set.ref().addElement("a");
				set2.ref().addElement("b");
				hashMap.ref().put("A",set.ref());
				hashMap.ref().put("A",set2.ref());
				String y = hashMap.ref().get("A").toString();
				System.out.println(y);
		}
>>>>>>> 02160a0b2053e5b64b23be342691dd274ccf3dc0
	}

	@Override
	public void cleanup() {
		system().clear(Sets.newHashSet());
	}


}
