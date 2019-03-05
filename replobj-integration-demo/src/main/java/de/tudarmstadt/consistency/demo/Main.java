package de.tudarmstadt.consistency.demo;


import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.demo.schema.ObjA;
import de.tudarmstadt.consistency.replobj.ConsistencyLevels;
import de.tudarmstadt.consistency.replobj.java.JRef;
import de.tudarmstadt.consistency.replobj.java.JReplicaSystem;

/**
 * Created on 29.05.18.
 *
 * @author Mirko Köhler
 */
public class Main {


	public static void main(String... args) throws Exception {

		JReplicaSystem replicaSystem1 = JReplicaSystem.fromActorSystem(2552);
		JReplicaSystem replicaSystem2 = JReplicaSystem.fromActorSystem(2553);

		replicaSystem1.addReplicaSystem("127.0.0.1", 2553);
		replicaSystem2.addReplicaSystem("127.0.0.1", 2552);


		JRef<@Strong ObjA> ref1Strong = replicaSystem1.<@Strong ObjA>replicate("os", (@Strong ObjA) new ObjA(), ConsistencyLevels.Strong.class);
		JRef<@Strong ObjA> ref2Strong = replicaSystem2.<@Strong ObjA>ref("os", (Class<@Strong ObjA>) ObjA.class, ConsistencyLevels.Strong.class);

		JRef<@Weak ObjA> ref1Weak = replicaSystem1.replicate("ow", (@Weak ObjA) new ObjA(), ConsistencyLevels.Weak.class);
		JRef<@Weak ObjA> ref2Weak = replicaSystem2.ref("ow", (Class<@Weak ObjA>) ObjA.class, ConsistencyLevels.Weak.class);


		Thread.sleep(3000);

		ref1Strong.setField("f", 34);
		ref1Weak.setField("f", 42);

//		int i = ref1Strong.getField("f");

		System.out.println("ref1Strong.f = "  + ref1Strong.getField("f"));
		System.out.println("ref2Strong.f = "  + ref2Strong.getField("f"));

		System.out.println("ref1Weak.f = "  + ref1Weak.getField("f"));
		System.out.println("ref2Weak.f = "  + ref2Weak.getField("f"));

		ref2Weak.synchronize();

		System.out.println("ref1Weak.f = "  + ref1Weak.getField("f"));
		System.out.println("ref2Weak.f = "  + ref2Weak.getField("f"));

		ref1Strong.setField("f", ref1Weak.getField("f"));



//		try (CassandraDatabase database = CassandraDatabase.local()) {
//
//			UUID id1 = new UUID(573489594L, 8675789563L);
//			UUID id2 = new UUID(573489512L, 1675789528L);
//			UUID id3 = new UUID(573489456L, 1675789879L);
//			UUID id4 = new UUID(573489465L, 1675789841L);
//
//			database.commit(context -> {
//				CassandraRef<@Strong de.tudarmstadt.consistency.demo.data.A> strongA = context.<@Strong de.tudarmstadt.consistency.demo.data.A>obtain(id1, de.tudarmstadt.consistency.demo.data.A.class, Strong.class);
//				CassandraRef<@Strong B> strongB = context.<@Strong B>obtain(id2, B.class, Strong.class);
//
//				//Types are correct: writing a local value to strong1/2 (strong)
//				strongA.write(new de.tudarmstadt.consistency.demo.data.A(312, strongB, "hello"));
//				strongB.write(new B("world"));
//
//				de.tudarmstadt.consistency.demo.data.A aStrong = strongA.read();
//				B bStrong = strongB.read();
//
//
//				Log.info(Main.class, aStrong);
//				Log.info(Main.class, bStrong);
//				Log.info(Main.class, aStrong.b.read());
//
//
//				CassandraRef<@Weak B> weakB = context.<@Weak B>obtain(id3, B.class, Weak.class);
//
//				weakB.write(new @Local B("moon"));
//
//				B bWeak = weakB.read();
//
//				//Type clash: writing weak value to strong handle
//				//strongB.write(bWeak);
//
//
//				//Types are correct: writing a strong value to a weak handle
//				weakB.write(bStrong);
//
//				//Type clash: Checking implicit flows
//				if (weakB.read() == null) {
//					//	A a = new @Strong A(213, strong2,"fire");
//					//	strong1.write(a);
//				}
//
//				CassandraRef<@Strong O> o1 = context.<@Strong O>obtain(id4, O.class, Strong.class);
//				o1.write(new O(new A(31, weakB, "lol"), "rofl"));
//				O o = o1.read();
//
//				Log.info(Main.class, o);
//				Log.info(Main.class, o.a.b.read());
//			}, null);
//		}
	}
}
