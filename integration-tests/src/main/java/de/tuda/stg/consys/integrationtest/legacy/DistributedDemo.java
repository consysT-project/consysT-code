package de.tuda.stg.consys.integrationtest.legacy;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.core.store.utils.Address;
import de.tuda.stg.consys.integrationtest.legacy.schema.ObjA;
import de.tuda.stg.consys.japi.legacy.JConsistencyLevels;
import de.tuda.stg.consys.japi.legacy.JRef;
import de.tuda.stg.consys.japi.legacy.JReplicaSystem;
import de.tuda.stg.consys.japi.legacy.impl.JReplicaSystems;

import java.util.Arrays;

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
		JReplicaSystem sys = JReplicaSystems.fromActorSystem(
			new Address("127.0.0.1", 3344),
			Arrays.asList(new Address("127.0.0.1", 3344), new Address("127.0.0.1", 3345))
		);

		try {
			JRef<@Strong ObjA> counter = sys.replicate("counter", new ObjA(), JConsistencyLevels.STRONG);

			counter.ref().inc();
			System.out.println("value = " + counter.ref().f);

			Thread.sleep(1000);
		} finally {
			sys.close();
		}

	}

	private static void replica1Code() throws Exception {
		JReplicaSystem sys = JReplicaSystems.fromActorSystem(
			new Address("127.0.0.1", 3345),
			Arrays.asList(new Address("127.0.0.1", 3344), new Address("127.0.0.1", 3345))
		);

		try {
			JRef<@Strong ObjA> counter = sys.lookup("counter", (Class<@Strong ObjA>) ObjA.class, JConsistencyLevels.STRONG);

			counter.ref().inc();
			System.out.println("value = " + counter.ref().f);

			Thread.sleep(1000);
		} finally {
			sys.close();
		}
	}
}
