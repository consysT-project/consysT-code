package de.tudarmstadt.consistency.replobj;

import akka.actor.ActorSystem;
import de.tudarmstadt.consistency.replobj.actors.AkkaReplicaSystem;
import de.tudarmstadt.consistency.replobj.actors.ReplicaSystems;

/**
 * Created on 01.03.19.
 *
 * @author Mirko Köhler
 */
public class JavaDemo {


	public static void main(String[] args) {

		ActorSystem actorSystem = ActorSystem.create("java-test");
		AkkaReplicaSystem<String> replicaSystem = ReplicaSystems.fromActors(actorSystem, "replica1");

		Ref<String, SomeObj, ConsistencyLevels.Weak> ref = replicaSystem.replicate("a", new SomeObj(), SomeObj.class, ConsistencyLevels.Weak.class);

		int i = ref.remote().f; //ref.toReplicatedObject().getField("f");

		ref.toReplicatedObject().setField("f", 45);

		int i2 = ref.toReplicatedObject().getField("f");

		System.out.println("i = " + i + ", i2 = " + i2);
	}
}
