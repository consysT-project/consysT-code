package objects;

import akka.actor.ActorSystem;
import de.tuda.stg.consys.objects.actors.AkkaReplicaSystem;
import de.tuda.stg.consys.objects.actors.package$;

/**
 * Created on 01.03.19.
 *
 * @author Mirko Köhler
 */
public class ReplicaSystems {

	public static AkkaReplicaSystem<String> fromActorSystem(ActorSystem actorSystem) {
		return package$.MODULE$.createReplicaSystem(actorSystem);
	}

	public static AkkaReplicaSystem<String> fromActorSystem(int port) {
		return package$.MODULE$.createReplicaSystem(port);
	}

	public static AkkaReplicaSystem<String> fromActorSystem(String hostname, int port) {
		return package$.MODULE$.createReplicaSystem(hostname, port);
	}

}

