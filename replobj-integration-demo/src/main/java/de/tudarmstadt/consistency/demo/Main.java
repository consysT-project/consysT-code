package de.tudarmstadt.consistency.demo;


import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.demo.schema.ObjA;
import de.tudarmstadt.consistency.demo.schema.ObjB;
import de.tudarmstadt.consistency.replobj.ConsistencyLevels;
import de.tudarmstadt.consistency.replobj.java.JRef;
import de.tudarmstadt.consistency.replobj.java.JReplicaSystem;

/**
 * Created on 29.05.18.
 *
 * @author Mirko Köhler
 */
public class Main {

	public static void example1() throws InterruptedException {
		JReplicaSystem replicaSystem1 = JReplicaSystem.fromActorSystem(2552);
		JReplicaSystem replicaSystem2 = JReplicaSystem.fromActorSystem(2553);

		replicaSystem1.addReplicaSystem("127.0.0.1", 2553);
		replicaSystem2.addReplicaSystem("127.0.0.1", 2552);


		JRef<@Strong ObjA> ref1Strong = replicaSystem1.replicate("os", new ObjA(), ConsistencyLevels.Strong.class);
		JRef<@Strong ObjA> ref2Strong = replicaSystem2.ref("os", (Class<@Strong ObjA>) ObjA.class, ConsistencyLevels.Strong.class);

		JRef<@Weak ObjA> ref1Weak = replicaSystem1.replicate("ow", new ObjA(), ConsistencyLevels.Weak.class);
		JRef<@Weak ObjA> ref2Weak = replicaSystem2.ref("ow", (Class<@Weak ObjA>) ObjA.class, ConsistencyLevels.Weak.class);


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

		JReplicaSystem replicaSystem1 = JReplicaSystem.fromActorSystem(2552);
		JReplicaSystem replicaSystem2 = JReplicaSystem.fromActorSystem(2553);

		replicaSystem1.addReplicaSystem("127.0.0.1", 2553);
		replicaSystem2.addReplicaSystem("127.0.0.1", 2552);


		JRef<@Strong ObjA> a1 = replicaSystem1.replicate("a", new ObjA(), ConsistencyLevels.Strong.class);
		JRef<@Weak ObjB> b1 = replicaSystem1.replicate("b", new ObjB(a1), ConsistencyLevels.Weak.class);

		JRef<@Strong ObjA> a2 = replicaSystem2.ref("a", (Class<@Strong ObjA>) ObjA.class, ConsistencyLevels.Strong.class);
		JRef<@Weak ObjB> b2 = replicaSystem2.ref("b", (Class<@Weak ObjB>) ObjB.class, ConsistencyLevels.Weak.class);

		Thread.sleep(2000);

		b1.invoke("incAll"); //n1

		System.out.println("#1");
		System.out.println("a1 = " + a1.getField("f"));
		System.out.println("b1 = " + b1.getField("g"));
		System.out.println("a2 = " + a2.getField("f"));
		System.out.println("b2 = " + b2.getField("g"));

		b2.sync();

		System.out.println("#2");
		System.out.println("a1 = " + a1.getField("f"));
		System.out.println("b1 = " + b1.getField("g"));
		System.out.println("a2 = " + a2.getField("f"));
		System.out.println("b2 = " + b2.getField("g"));


		b2.invoke("incAll");

		System.out.println("#3");
		System.out.println("a1 = " + a1.getField("f"));
		System.out.println("b1 = " + b1.getField("g"));
		System.out.println("a2 = " + a2.getField("f"));
		System.out.println("b2 = " + b2.getField("g"));


		b2.sync();

		System.out.println("#4");
		System.out.println("a1 = " + a1.getField("f"));
		System.out.println("b1 = " + b1.getField("g"));
		System.out.println("a2 = " + a2.getField("f"));
		System.out.println("b2 = " + b2.getField("g"));


	}


	public static void example2Small() throws InterruptedException {

		JReplicaSystem replicaSystem1 = JReplicaSystem.fromActorSystem(2552);
		JReplicaSystem replicaSystem2 = JReplicaSystem.fromActorSystem(2553);

		replicaSystem1.addReplicaSystem("127.0.0.1", 2553);
		replicaSystem2.addReplicaSystem("127.0.0.1", 2552);


		JRef<@Strong ObjA> a1 = replicaSystem1.replicate("a", new ObjA(), ConsistencyLevels.Strong.class);
		JRef<@Weak ObjB> b1 = replicaSystem1.replicate("b", new ObjB(a1), ConsistencyLevels.Weak.class);

		JRef<@Strong ObjA> a2 = replicaSystem2.ref("a", (Class<@Strong ObjA>) ObjA.class, ConsistencyLevels.Strong.class);
		JRef<@Weak ObjB> b2 = replicaSystem2.ref("b", (Class<@Weak ObjB>) ObjB.class, ConsistencyLevels.Weak.class);

		Thread.sleep(2000);

		b1.invoke("incAll"); //n1

		b2.invoke("incAll");

		b2.sync();

		System.out.println("#4");
		System.out.println("a1 = " + a1.getField("f"));
		System.out.println("b1 = " + b1.getField("g"));
		System.out.println("a2 = " + a2.getField("f"));
		System.out.println("b2 = " + b2.getField("g"));


	}

	public static void main(String... args) throws Exception {
		example2Small();
	}
}
