package de.tuda.stg.consys.japi.impl.akka;

import de.tuda.stg.consys.checker.qual.Local;
import de.tuda.stg.consys.core.ConsistencyLevel;
import de.tuda.stg.consys.core.Ref;
import de.tuda.stg.consys.core.akka.AkkaReplicaSystem;
import de.tuda.stg.consys.japi.*;
import scala.collection.JavaConverters;

import java.time.Duration;
import java.util.HashSet;
import java.util.Set;

/**
 * Java wrapper around {@link AkkaReplicaSystem}.
 *
 * @author Mirko Köhler
 */
public class JAkkaReplicaSystem implements JReplicaSystem,
	JReplicaSystemWithRemove,
	JReplicaSystemWithBarrier {

	public final AkkaReplicaSystem replicaSystem;

	public JAkkaReplicaSystem(AkkaReplicaSystem replicaSystem) {
		this.replicaSystem = replicaSystem;
	}


	@Override
	public <T> JRef<T> replicate(String addr, @Local T obj, ConsistencyLevel consistencyLevel) {
		Class<T> objCls = (Class<T>) obj.getClass();
		Ref<String, T> ref = replicaSystem.replicate(addr, obj, objCls, consistencyLevel);

		return new JAkkaRef<>(ref);
	}

	@Override
	public <T> JRef<T> replicate(@Local T obj, ConsistencyLevel consistencyLevel) {
		Class<T> objCls = (Class<T>) obj.getClass();
		Ref<String, T> ref = replicaSystem.replicate(obj, objCls, consistencyLevel);

		return new JAkkaRef<>(ref);
	}

	@Override
	public <T> JRef<T> lookup(String addr, Class<T> objCls, ConsistencyLevel consistencyLevel) {
		Ref<String, T> ref = replicaSystem.lookup(addr, objCls, consistencyLevel);
		return new JAkkaRef<>(ref);
	}

	@Override
	public void remove(String addr) {
		replicaSystem.delete(addr);
	}


	@Override
	public void close() throws Exception {
		replicaSystem.close();
	}

	@Override
	public int numOfReplicas() {
		return replicaSystem.getOtherReplicas().size();
	}

	@Override
	public void clear(Set<String> except) {
		replicaSystem.clear(JavaConverters.asScalaSet(except).toSet());
	}

	@Override
	public void clear() {
		replicaSystem.clear(JavaConverters.<String>asScalaSet(new HashSet<>()).toSet());
	}


	@Override
	public void barrier(String name) {
		replicaSystem.barrier(name);
	}

	@Override
	public void barrier(String name, Duration timeout) {
		replicaSystem.barrier(name, scala.concurrent.duration.Duration.fromNanos(timeout.toNanos()));
	}

	@Override
	public int numberOfObjects() {
		return replicaSystem.numberOfObjects();
	}

	@Override
	public long timeoutInMillis() {
		return replicaSystem.defaultTimeout().toMillis();
	}

	@Override
	public boolean equals(Object other) {
		return other instanceof JAkkaReplicaSystem
			&& ((JAkkaReplicaSystem) other).replicaSystem == replicaSystem;
	}

	@Override
	public int hashCode() {
		return replicaSystem.hashCode();
	}

	@Override
	public String toString() {
		return "Wrapped(" + replicaSystem + ")";
	}
}
