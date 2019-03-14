package de.tudarmstadt.consistency.demo;


import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.demo.schema.ObjA;
import de.tudarmstadt.consistency.demo.schema.ObjB;
import de.tudarmstadt.consistency.replobj.java.JConsistencyLevel;
import de.tudarmstadt.consistency.replobj.java.JRef;

import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

import static de.tudarmstadt.consistency.demo.Replicas.replicaSystem1;
import static de.tudarmstadt.consistency.demo.Replicas.replicaSystem2;

/**
 * Created on 29.05.18.
 *
 * @author Mirko Köhler
 */
public class Main {



	public static void example1() throws InterruptedException {

		JRef<@Strong ObjA> ref1Strong = replicaSystem1.replicate("os", new ObjA(), JConsistencyLevel.STRONG);
		JRef<@Strong ObjA> ref2Strong = replicaSystem2.ref("os", (Class<@Strong ObjA>) ObjA.class, JConsistencyLevel.STRONG);

		JRef<@Weak ObjA> ref1Weak = replicaSystem1.replicate("ow", new ObjA(), JConsistencyLevel.WEAK);
		JRef<@Weak ObjA> ref2Weak = replicaSystem2.ref("ow", (Class<@Weak ObjA>) ObjA.class, JConsistencyLevel.WEAK);


		Thread.sleep(3000);

		ref1Strong.setField("f", 34);
		ref1Weak.setField("f", 42);

		int i = ref1Strong.getField("f"); //.getField("f");

		ref1Strong.setField("f", 42);

		ref1Strong.invoke("inc");
		ref1Strong.invoke("incBy", 4 + 21);

		ref1Strong.invoke("incBy", 4 + (21 * 13) );


		System.out.println("ref1Strong.f = "  + ref1Strong.getField("f"));
		System.out.println("ref2Strong.f = "  + ref2Strong.getField("f"));

		System.out.println("ref1Weak.f = "  + ref1Weak.getField("f"));
		System.out.println("ref2Weak.f = "  + ref2Weak.getField("f"));

		ref2Weak.sync();

		System.out.println("ref1Weak.f = "  + ref1Weak.getField("f"));
		System.out.println("ref2Weak.f = "  + ref2Weak.getField("f"));

		ref1Strong.setField("f", ref1Weak.getField("f"));
	}


	public static void example2() throws InterruptedException {


		JRef<@Strong ObjA> a1 = replicaSystem1.replicate("a", new ObjA(), JConsistencyLevel.STRONG);
		JRef<@Weak ObjB> b1 = replicaSystem1.replicate("b", new ObjB(a1), JConsistencyLevel.WEAK);

		JRef<@Strong ObjA> a2 = replicaSystem2.ref("a", (Class<@Strong ObjA>) ObjA.class, JConsistencyLevel.STRONG);
		JRef<@Weak ObjB> b2 = replicaSystem2.ref("b", (Class<@Weak ObjB>) ObjB.class, JConsistencyLevel.WEAK);

		Thread.sleep(2000);

		b1.invoke("incAll");
		b2.invoke("incAll");


		System.out.println("#1");

		Object[] results1 = new Object[] {
				a1.getField("f"),
				a2.getField("f"),
				b1.getField("g"),
				b2.getField("g")
		};

		System.out.println(
				"a1.f = " + results1[0] + ", " +
						"a2.f = " + results1[1] + ", " +
						"b1.g = " + results1[2] + ", " +
						"b2.g = " + results1[3]
		);


		b2.sync();

		System.out.println("#2");

		Object[] results2 = new Object[] {
				a1.getField("f"),
				a2.getField("f"),
				b1.getField("g"),
				b2.getField("g")
		};

		System.out.println(
			"a1.f = " + results2[0] + ", " +
			"a2.f = " + results2[1] + ", " +
			"b1.g = " + results2[2] + ", " +
			"b2.g = " + results2[3]
		);
	}

	public static void example2Parallel() throws InterruptedException {


		JRef<@Strong ObjA> a1 = replicaSystem1.replicate("a", new ObjA(), JConsistencyLevel.STRONG);
		JRef<@Weak ObjB> b1 = replicaSystem1.replicate("b", new ObjB(a1), JConsistencyLevel.WEAK);

		JRef<@Strong ObjA> a2 = replicaSystem2.ref("a", (Class<@Strong ObjA>) ObjA.class, JConsistencyLevel.STRONG);
		JRef<@Weak ObjB> b2 = replicaSystem2.ref("b", (Class<@Weak ObjB>) ObjB.class, JConsistencyLevel.WEAK);

		Thread.sleep(2000);


		ExecutorService exec = Executors.newFixedThreadPool(4);
		Future<Void> fut1 = exec.submit(() -> b1.invoke("incAll"));
		Future<Void> fut2 = exec.submit(() -> b2.invoke("incAll"));

		Thread.sleep(3000);

		System.out.println("#1");

		Object[] results1 = new Object[] {
				a1.getField("f"),
				a2.getField("f"),
				b1.getField("g"),
				b2.getField("g")
		};

		System.out.println(
				"a1.f = " + results1[0] + ", " +
						"a2.f = " + results1[1] + ", " +
						"b1.g = " + results1[2] + ", " +
						"b2.g = " + results1[3]
		);


		b2.sync();

		System.out.println("#2");

		Object[] results2 = new Object[] {
				a1.getField("f"),
				a2.getField("f"),
				b1.getField("g"),
				b2.getField("g")
		};

		System.out.println(
				"a1.f = " + results2[0] + ", " +
						"a2.f = " + results2[1] + ", " +
						"b1.g = " + results2[2] + ", " +
						"b2.g = " + results2[3]
		);
	}

	public static void main(String... args) throws Exception {
		example2Parallel();
	}
}
