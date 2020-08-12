package de.tuda.stg.consys.demo.dcrdt;

import com.typesafe.config.Config;
import de.tuda.stg.consys.demo.Demo;
import de.tuda.stg.consys.demo.DemoBenchmark;
import de.tuda.stg.consys.demo.dcrdt.schema.*;
import de.tuda.stg.consys.japi.JConsistencyLevels;
import de.tuda.stg.consys.japi.JRef;
import org.checkerframework.com.google.common.collect.Sets;
import scala.Option;

/**
 * @author = Kris Frühwein, Julius Näumann
 * Integer vetor that only grows
 */
public class DCRDTBenchmark extends DemoBenchmark {
	public static void main(String[] args) {
		start(DCRDTBenchmark.class, args);
	}

	public DCRDTBenchmark(Config config) {
		super(config, Option.empty());
	}

	private JRef<StringHashmap> map;
	private JRef<DotStoreString> dotStore;

	private JRef<AddOnlySetString> set;

	private JRef<AddOnlySetString> set2;

	private JRef<AddRemoveSet> addRemove;

	private JRef<IntegerVector> vector;

	private  JRef<DCRDTHashMap> hashMap;

	private int switcher = 4;

	@Override
	public void setup() {
		switch (switcher) {
			case 0:
				if (processId() == 0) {
					dotStore = system().replicate("dotstore", new DotStoreString(), JConsistencyLevels.DCRDT);
				} else {
					dotStore = system().lookup("dotstore", DotStoreString.class, JConsistencyLevels.DCRDT);
					dotStore.sync(); //Force dereference
				}
				System.out.println(processId() + " finished setup of dotStore");
				break;

			case 1:
				if (processId() == 0) {
					set = system().replicate("aoset", new AddOnlySetString(), JConsistencyLevels.DCRDT);
				} else {
					set = system().lookup("aoset", AddOnlySetString.class, JConsistencyLevels.DCRDT);
					set.sync(); //Force dereference
				}
				System.out.println(processId() + " finished setup of set");
				break;

			case 2:
				if (processId() == 0) {
					addRemove = system().replicate("arset", new AddRemoveSet(), JConsistencyLevels.DCRDT);
				} else {
					addRemove = system().lookup("arset", AddRemoveSet.class, JConsistencyLevels.DCRDT);
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
					hashMap = system().replicate("hashmap", new DCRDTHashMap(), JConsistencyLevels.DCRDT);

				} else {
					hashMap = system().lookup("hashmap", DCRDTHashMap.class, JConsistencyLevels.DCRDT);
					hashMap.sync(); //Force dereference
				}
				System.out.println(processId() + " finished setup of HashMap");
				break;
			case 5:
				if (processId() == 0) {
					map = system().replicate("hashmap", new StringHashmap(), JConsistencyLevels.DCRDT);
				} else {
					map = system().<StringHashmap>lookup("hashmap", StringHashmap.class, JConsistencyLevels.DCRDT);
					map.sync(); //Force dereference

				}
				break;
		}

	}

	@Override
	public void operation() {
		switch (switcher) {
			case 0:
				dotStore.ref().addString("Hello from " + processId(), processId());
				dotStore.ref().removeString("Hello from " + processId(), processId());
				String s = "current String of" + processId() +" after removal: "+dotStore.ref().toString(processId());
				System.out.println(s);
				doSync(() -> dotStore.sync());
				System.out.print(".");
				break;
			case 1:
				set.ref().addElement("Hello from "+ processId() );
				doSync(() -> set.sync());
				System.out.print(".");
				break;

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
				AddOnlySetString strset = new AddOnlySetString();
				strset.addElement("a" + processId());
				AddOnlySetString strset2 = new AddOnlySetString();
				strset2.addElement("b" + processId());
				hashMap.ref().put("KEY",strset);
				hashMap.ref().put("KEY"+processId(),strset2);
				break;

			case 5:
				map.ref().addEntry("Key " + processId(), "Value " + processId());

				doSync(() -> map.sync());
				System.out.print(".");
				break;
		}
	}

	@Override
	public void cleanup() {
		system().clear(Sets.newHashSet());
	}


}
