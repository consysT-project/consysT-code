package de.tuda.stg.consys.demo;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.demo.schema.ObjA;
import de.tuda.stg.consys.objects.japi.JConsistencyLevels;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;
import de.tuda.stg.consys.objects.japi.JReplicaSystems;

/**
 * Created on 31.07.19.
 *
 * @author Mirko Köhler
 */
public class DistributedDemo {

	public static void main(String... args) throws Exception {
		if (args[0].equals("0")) {
			replica0Code();
		} else if (args[0].equals("1")) {
			replica1Code();
		}
	}

	private static void replica0Code() throws Exception {
		JReplicaSystem sys = JReplicaSystems.fromActorSystem("127.0.0.1", 3344);

		try {
			Thread.sleep(5000);

			sys.addReplicaSystem("127.0.0.1", 3345);

			Thread.sleep(5000);

			JRef<@Strong ObjA> counter = sys.replicate("counter", new ObjA(), JConsistencyLevels.STRONG);
			counter.ref().inc();
			System.out.println("value = " + counter.ref().f);

			Thread.sleep(10000);
		} finally {
			sys.close();
		}

	}

	private static void replica1Code() throws Exception {
		JReplicaSystem sys = JReplicaSystems.fromActorSystem("127.0.0.1", 3345);

		try {
			Thread.sleep(5000);

			sys.addReplicaSystem("127.0.0.1", 3344);

			Thread.sleep(10000);

			JRef<@Strong ObjA> counter = sys.lookup("counter", ObjA.class, JConsistencyLevels.STRONG);
			counter.ref().inc();
			System.out.println("value = " + counter.ref().f);

			Thread.sleep(5000);
		} finally {
			sys.close();
		}
	}
}
