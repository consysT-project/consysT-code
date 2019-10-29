package de.tuda.stg.consys.objects.japi;

import de.tuda.stg.consys.objects.actors.AkkaReplicaSystem;

/**
 * Created on 01.03.19.
 *
 * @author Mirko Köhler
 */
public class Demo {


	static class SomeObj implements JReplicated {
		/* This field is needed for JReplicated */ public transient AkkaReplicaSystem<String> replicaSystem = null;

		public int f = 0;

		SomeObj(){
			showSystem();
		}

		public void showSystem() {
			System.out.println("system = " + getSystem());
		}

	}


	public static void main(String[] args) throws Exception {

		JReplicaSystem replicaSystem1 = JReplicaSystems.fromActorSystem(2552);
		JReplicaSystem replicaSystem2 = JReplicaSystems.fromActorSystem(2553);

		System.out.println("system1 = " + replicaSystem1);
		System.out.println("system2 = " + replicaSystem2);


		try {

			replicaSystem1.addReplicaSystem("127.0.0.1", 2553);
			replicaSystem2.addReplicaSystem("127.0.0.1", 2552);


			JRef<SomeObj> ref1Strong = replicaSystem1.replicate("os", new SomeObj(), JConsistencyLevels.STRONG);
			JRef<SomeObj> ref2Strong = replicaSystem2.lookup("os", SomeObj.class, JConsistencyLevels.STRONG);

			JRef<SomeObj> ref1Weak = replicaSystem1.replicate("ow", new SomeObj(), JConsistencyLevels.WEAK);
			JRef<SomeObj> ref2Weak = replicaSystem2.lookup("ow", SomeObj.class, JConsistencyLevels.WEAK);


			ref1Strong.setField("f", 34);
			ref1Weak.setField("f", 42);

//		int i = ref1Strong.getField("f");

			System.out.println("ref1Strong.f = " + ref1Strong.getField("f"));
			System.out.println("ref2Strong.f = " + ref2Strong.getField("f"));

			System.out.println("ref1Weak.f = " + ref1Weak.getField("f"));
			System.out.println("ref2Weak.f = " + ref2Weak.getField("f"));

			ref2Weak.sync();

			System.out.println("ref1Weak.f = " + ref1Weak.getField("f"));
			System.out.println("ref2Weak.f = " + ref2Weak.getField("f"));


			ref1Strong.invoke("showSystem");
			ref2Strong.invoke("showSystem");

			ref1Strong.delete();
			ref2Strong.getField("f");

		} finally {
			replicaSystem1.close();
			replicaSystem2.close();
		}
	}
}
