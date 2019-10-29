package de.tuda.stg.consys.objects.japi;

import akka.actor.ActorSystem;
import de.tuda.stg.consys.checker.qual.Local;
import de.tuda.stg.consys.objects.ConsistencyLevel;

import java.time.Duration;
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

	void remove(String addr);

	void addReplicaSystem(String hostname, int port);

	void close() throws Exception;

	int numOfReplicas();

	void clear(Set<String> except);

	void barrier(String name);

	void barrier(String name, Duration timeout);


}

