package de.tudarmstadt.consistency.replobj;

import akka.actor.ActorSystem;
import de.tudarmstadt.consistency.replobj.Ref;
import de.tudarmstadt.consistency.replobj.actors.AkkaReplicaSystem;
import de.tudarmstadt.consistency.replobj.actors.AkkaReplicaSystem$;

/**
 * Created on 01.03.19.
 *
 * @author Mirko Köhler
 */
public class ReplicaSystems {

	public static <Addr> AkkaReplicaSystem<Addr> fromActorSystem(ActorSystem actorSystem) {
		return AkkaReplicaSystem$.MODULE$.create(actorSystem);
	}

	public static <Addr> AkkaReplicaSystem<Addr> fromActorSystem(int port) {
		return AkkaReplicaSystem$.MODULE$.create(port);
	}

}

