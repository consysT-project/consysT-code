package de.tuda.stg.consys.demo;


import de.tuda.stg.consys.demo.schema.ObjA;
import de.tuda.stg.consys.demo.schema.ObjB;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.objects.japi.JConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;
import org.checkerframework.com.google.common.collect.Lists;

import java.util.Iterator;
import java.util.List;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;

/**
 * Created on 29.05.18.
 *
 * @author Mirko Köhler
 */
public class Main {

	private static class ReplicaParams {
		public final String addr;
		public final int port;

		private ReplicaParams(String addr, int port) {
			this.addr = addr;
			this.port = port;
		}
	}

	private static List<ReplicaParams> createParams(List<String> stringArgs) {
		List<ReplicaParams> result = Lists.newLinkedList();

		Iterator<String> it = stringArgs.iterator();
		while(it.hasNext()) {
			String addr = it.next();
			int port = Integer.parseInt(it.next());

			result.add(new ReplicaParams(addr, port));
		}
		return result;
	}

	public static void main(String... args) throws Exception {
//		List<ReplicaParams> argList = createParams(Arrays.asList(args));
//		distributedExample(argList.get(0), argList.subList(1, argList.size()));
		example2Parallel();

	}


	public static void distributedExample(ReplicaParams thisReplica, Iterable<ReplicaParams> otherReplicas) throws InterruptedException {
		JReplicaSystem sys = JReplicaSystem.fromActorSystem(thisReplica.addr, thisReplica.port);

		Thread.sleep(5000);

		for (ReplicaParams otherRepplica : otherReplicas) {
			sys.addReplicaSystem(otherRepplica.addr, otherRepplica.port);
		}

		Thread.sleep(5000);

		JRef<@Strong ObjA> a = sys.replicate(new ObjA(), JConsistencyLevel.STRONG);
		System.out.println("Invoke: " + a.ref().incBy(631));
		System.out.println("Value: " + a.ref().f);
	}

	public static void example1() throws Exception {
		JRef<@Strong ObjA> ref1Strong = Replicas.replicaSystem1.replicate("os", new ObjA(), JConsistencyLevel.STRONG);
		JRef<@Weak ObjA> ref1Weak = Replicas.replicaSystem1.replicate("ow", new ObjA(), JConsistencyLevel.WEAK);

		JRef<@Strong ObjA> ref2Strong = Replicas.replicaSystem2.lookup("os", (Class<@Strong ObjA>) ObjA.class, JConsistencyLevel.STRONG);
		JRef<@Weak ObjA> ref2Weak = Replicas.replicaSystem2.lookup("ow", (Class<@Weak ObjA>) ObjA.class, JConsistencyLevel.WEAK);


		ref1Strong.ref().f = 34;
		ref1Weak.ref().f = 42;
		ref1Strong.ref().f = 42;

		ref1Strong.ref().inc();
		ref1Strong.ref().incBy(4 + 21);
		ref1Strong.ref().incBy(4 + (21 * 13) );


		System.out.println("ref1Strong.f = "  + ref1Strong.ref().f);
		System.out.println("ref2Strong.f = "  + ref2Strong.ref().f);

		System.out.println("ref1Weak.f = "  + ref1Weak.ref().f);
		System.out.println("ref2Weak.f = "  + ref2Weak.ref().f);

		// This (expectedly) gives a type error!
		// ref2Strong.ref().f = ref2Weak.ref().f;

		ref2Weak.syncAll();

		System.out.println("ref1Weak.f = "  + ref1Weak.ref().f);
		System.out.println("ref2Weak.f = "  + ref2Weak.ref().f);

		ref1Strong.ref().f = ref1Weak.ref().f;

		Replicas.replicaSystem1.close();
		Replicas.replicaSystem2.close();
	}

// Desugared version of example1
//	public static void example1() throws Exception {
//
//		JRef<@Strong ObjA> ref1Strong = replicaSystem1.replicate("os", new ObjA(), JConsistencyLevel.STRONG);
//		JRef<@Strong ObjA> ref2Strong = replicaSystem2.ref("os", (Class<@Strong ObjA>) ObjA.class, JConsistencyLevel.STRONG);
//
//		JRef<@Weak ObjA> ref1Weak = replicaSystem1.replicate("ow", new ObjA(), JConsistencyLevel.WEAK);
//		JRef<@Weak ObjA> ref2Weak = replicaSystem2.ref("ow", (Class<@Weak ObjA>) ObjA.class, JConsistencyLevel.WEAK);
//
//
//		ref1Strong.setField("f", 34);
//		ref1Weak.setField("f", 42);
//		ref1Strong.setField("f", 42);
//
//		ref1Strong.invoke("inc");
//		ref1Strong.invoke("incBy", 4 + 21);
//		ref1Strong.invoke("incBy", new Object[] {} );
//
//
//		System.out.println("ref1Strong.f = "  + ref1Strong.getField("f"));
//		System.out.println("ref2Strong.f = "  + ref2Strong.getField("f"));
//
//		System.out.println("ref1Weak.f = "  + ref1Weak.getField("f"));
//		System.out.println("ref2Weak.f = "  + ref2Weak.getField("f"));
//
//		ref2Weak.syncAll();
//
//		System.out.println("ref1Weak.f = "  + ref1Weak.getField("f"));
//		System.out.println("ref2Weak.f = "  + ref2Weak.getField("f"));
//
//		ref1Strong.setField("f", ref1Weak.getField("f"));
//
//		replicaSystem1.close();
//		replicaSystem2.close();
//	}


	public static void example2() throws Exception {


		JRef<@Strong ObjA> a1 = Replicas.replicaSystem1.replicate("a", new ObjA(), JConsistencyLevel.STRONG);
		JRef<@Weak ObjB> b1 = Replicas.replicaSystem1.replicate("b", new ObjB(a1), JConsistencyLevel.WEAK);

		JRef<@Strong ObjA> a2 = Replicas.replicaSystem2.lookup("a", (Class<@Strong ObjA>) ObjA.class, JConsistencyLevel.STRONG);
		JRef<@Weak ObjB> b2 = Replicas.replicaSystem2.lookup("b", (Class<@Strong ObjB>) ObjB.class, JConsistencyLevel.WEAK);

		b1.ref().incAll();
		b2.ref().incAll();

		System.out.println("#1");
		System.out.println(
			"a1.f = " + a1.ref().f + ", " +
			"a2.f = " + a2.ref().f + ", " +
			"b1.g = " + b1.ref().g + ", " +
			"b2.g = " + b2.ref().g
		);


		b2.syncAll();

		System.out.println("#2");
		System.out.println(
			"a1.f = " + a1.ref().f + ", " +
			"a2.f = " + a2.ref().f + ", " +
			"b1.g = " + b1.ref().g + ", " +
			"b2.g = " + b2.ref().g
		);

		Replicas.replicaSystem1.close();
		Replicas.replicaSystem2.close();
	}

	public static void example2Parallel() throws Exception {


		JRef<@Strong ObjA> a1 = Replicas.replicaSystem1.replicate("a", new ObjA(), JConsistencyLevel.STRONG);
		JRef<@Weak ObjB> b1 = Replicas.replicaSystem1.replicate("b", new ObjB(a1), JConsistencyLevel.WEAK);

		JRef<@Strong ObjA> a2 = Replicas.replicaSystem2.lookup("a", (Class<@Strong ObjA>) ObjA.class, JConsistencyLevel.STRONG);
		JRef<@Weak ObjB> b2 = Replicas.replicaSystem2.lookup("b", (Class<@Weak ObjB>) ObjB.class, JConsistencyLevel.WEAK);


		ExecutorService exec = Executors.newFixedThreadPool(4);
		Future<?> fut1 = exec.submit(
			() -> b1.ref().incAll()
		);
		Future<?> fut2 = exec.submit(
			() -> b2.ref().incAll()
		);

		exec.shutdown();
		exec.awaitTermination(10, TimeUnit.SECONDS);


		System.out.println("#1");
		System.out.println(
			"a1.f = " + a1.ref().f + ", " +
				"a2.f = " + a2.ref().f + ", " +
				"b1.g = " + b1.ref().g + ", " +
				"b2.g = " + b2.ref().g
		);



		b2.syncAll();

		System.out.println("#2");
		System.out.println(
			"a1.f = " + a1.ref().f + ", " +
				"a2.f = " + a2.ref().f + ", " +
				"b1.g = " + b1.ref().g + ", " +
				"b2.g = " + b2.ref().g
		);


		Replicas.replicaSystem1.close();
		Replicas.replicaSystem2.close();
	}


}
