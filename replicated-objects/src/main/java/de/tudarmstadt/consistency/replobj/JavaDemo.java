package de.tudarmstadt.consistency.replobj;

import java.io.Serializable;

/**
 * Created on 01.03.19.
 *
 * @author Mirko Köhler
 */
public class JavaDemo {


	public static void main(String[] args) {
		ReplicaSystem<String> replicaSystem = ReplicaSystems.fromActorSystem(2552);

		Ref<String, SomeObj, ConsistencyLevels.Weak> ref = replicaSystem.replicate("a", new SomeObj(), SomeObj.class, ConsistencyLevels.Weak.class);

		int i = ref.toReplicatedObject().getField("f");

		ref.toReplicatedObject().setField("f", 45);

		int i2 = ref.toReplicatedObject().getField("f");

		System.out.println("i = " + i + ", i2 = " + i2);
	}



	public static class SomeObj implements Serializable {
		public int f = 0;
	}
}
