package de.tudarmstadt.consistency.replobj;

import akka.actor.ActorSystem;
import de.tudarmstadt.consistency.replobj.actors.ActorReplicaSystem;
import de.tudarmstadt.consistency.replobj.actors.ActorReplicaSystem$;

/**
 * Created on 01.03.19.
 *
 * @author Mirko Köhler
 */
public class ReplicaSystems {

	public static <Addr> ActorReplicaSystem<Addr> fromActorSystem(ActorSystem actorSystem) {
		return ActorReplicaSystem$.MODULE$.create(actorSystem);
	}

	public static <Addr> ActorReplicaSystem<Addr> fromActorSystem(int port) {
		return ActorReplicaSystem$.MODULE$.create(port);
	}

}

