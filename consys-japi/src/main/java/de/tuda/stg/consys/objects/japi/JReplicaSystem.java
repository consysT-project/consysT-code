package de.tuda.stg.consys.objects.japi;

import akka.actor.ActorSystem;
import de.tuda.stg.consys.checker.qual.Local;
import de.tuda.stg.consys.objects.ConsistencyLevel;

import java.util.Set;


/**
 * Created on 01.03.19.
 *
 * @author Mirko Köhler
 */
public interface JReplicaSystem {

	<T> @Local JRef<T> replicate(String addr, @Local T obj, ConsistencyLevel consistencyLevel);

	<T> @Local JRef<T> replicate(@Local T obj, ConsistencyLevel consistencyLevel);

	<T> @Local JRef<T> lookup(String addr, Class<T> objCls, ConsistencyLevel consistencyLevel);

	void delete(String addr);

	void addReplicaSystem(String hostname, int port);

	void close() throws Exception;

	int numOfReplicas();

	void clear(Set<String> except);

	static JReplicaSystem fromActorSystem(ActorSystem actorSystem) {
		return new JReplicaSystemAkkaImpl(actorSystem);
	}

	static JReplicaSystem fromActorSystem(String hostname, int port) {
		return new JReplicaSystemAkkaImpl(hostname, port);
	}

	static JReplicaSystem fromActorSystem(int port) {
		return new JReplicaSystemAkkaImpl(port);
	}
}

