package de.tudarmstadt.consistency.replobj.actors;

import akka.actor.ActorSystem;
import de.tudarmstadt.consistency.replobj.Ref;

/**
 * Created on 01.03.19.
 *
 * @author Mirko Köhler
 */
public class ReplicaSystems {

	public static <Addr> AkkaReplicaSystem<Addr> fromActors(ActorSystem actorSystem, String name) {
		return AkkaReplicaSystem$.MODULE$.create(actorSystem, name);
	}

}

