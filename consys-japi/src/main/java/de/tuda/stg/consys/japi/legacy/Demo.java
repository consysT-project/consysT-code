package de.tuda.stg.consys.japi.legacy;


import de.tuda.stg.consys.core.legacy.akka.AkkaReplicaSystem;
import de.tuda.stg.consys.japi.legacy.impl.JReplicaSystems;

/**
 * Created on 01.03.19.
 *
 * @author Mirko Köhler
 */
public class Demo {


	static class SomeObj implements JReplicated {
		/* This field is needed for JReplicated */ public transient AkkaReplicaSystem replicaSystem = null;

		public int f = 0;

		SomeObj() {
			showSystem();
		}

		public void showSystem() {
			System.out.println("system = " + getSystem());
		}
	}


	public static void main(String[] args) throws Exception {
		JReplicaSystem[] replicas = JReplicaSystems.fromActorSystemForTesting(2);

		System.out.println("system1 = " + replicas[0]);
		System.out.println("system2 = " + replicas[1]);

		try {
			JRef<SomeObj> ref1Strong = replicas[0].replicate("os", new SomeObj(), JConsistencyLevels.STRONG);
			JRef<SomeObj> ref2Strong = replicas[1].lookup("os", SomeObj.class, JConsistencyLevels.STRONG);

			JRef<SomeObj> ref1Weak = replicas[0].replicate("ow", new SomeObj(), JConsistencyLevels.WEAK);
			JRef<SomeObj> ref2Weak = replicas[1].lookup("ow", SomeObj.class, JConsistencyLevels.WEAK);


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
			replicas[0].close();
			replicas[1].close();
		}
	}
}
