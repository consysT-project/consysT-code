package de.tuda.stg.consys.integrationtest;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.core.Address;
import de.tuda.stg.consys.integrationtest.schema.ObjA;
import de.tuda.stg.consys.japi.JConsistencyLevels;
import de.tuda.stg.consys.japi.JRef;
import de.tuda.stg.consys.japi.JReplicaSystem;
import de.tuda.stg.consys.japi.impl.JReplicaSystems;

import java.util.Arrays;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

/**
 * Created on 31.07.19.
 *
 * @author Mirko Köhler
 */
public class Demo {

	public static void main(String... args) throws Exception {
		ExecutorService exec = Executors.newFixedThreadPool(4);
		exec.submit(() -> {
			try {
				replica0Code();
			} catch (Exception e) {
				e.printStackTrace();
			}
		});
		exec.submit(() -> {
			try {
				replica1Code();
			} catch (Exception e) {
				e.printStackTrace();
			}
		});
	}

	private static void replica0Code() throws Exception {
		JReplicaSystems.withActorSystem(
				new Address("127.0.0.1", 3344),
				Arrays.asList(new Address("127.0.0.1", 3344), new Address("127.0.0.1", 3345))
		).use(() -> {
			JRef<@Strong ObjA> counter = JReplicaSystems.getSystem().replicate("counter", new ObjA(), JConsistencyLevels.STRONG);

			counter.ref().inc();
			System.out.println("value = " + counter.ref().f);

			return true;
		});
	}

	private static void replica1Code() throws Exception {
		JReplicaSystems.withActorSystem(
				new Address("127.0.0.1", 3344),
				Arrays.asList(new Address("127.0.0.1", 3344), new Address("127.0.0.1", 3345))
		).use(() -> {
			JRef<@Strong ObjA> counter = JReplicaSystems.getSystem().lookup("counter", (Class<@Strong ObjA>) ObjA.class, JConsistencyLevels.STRONG);

			counter.ref().inc();
			System.out.println("value = " + counter.ref().f);

			return true;
		});
	}
}
