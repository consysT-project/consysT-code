package de.tudarmstadt.consistency.replobj.java;

import akka.actor.ActorSystem;
import de.tudarmstadt.consistency.replobj.java.impl.JReplicaSystemAkkaImpl;

/**
 * Created on 01.03.19.
 *
 * @author Mirko Köhler
 */
public interface JReplicaSystem {

	<T> JRef<T> replicate(String addr, T obj, Class<?> consistencyCls);

	<T> JRef<T> ref(String addr, Class<T> objCls, Class<?> consistencyCls);

	void addReplicaSystem(String hostname, int port);

	static JReplicaSystem fromActorSystem(ActorSystem actorSystem) {
		return new JReplicaSystemAkkaImpl(actorSystem);
	}

	static JReplicaSystem fromActorSystem(int port) {
		return new JReplicaSystemAkkaImpl(port);
	}
}

