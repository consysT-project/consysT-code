package de.tuda.stg.consys.objects.japi;

import akka.actor.ActorSystem;
import de.tuda.stg.consys.checker.qual.Local;
import de.tuda.stg.consys.objects.ConsistencyLevel;
import de.tuda.stg.consys.objects.Ref;
import de.tuda.stg.consys.objects.ReplicaSystems;
import de.tuda.stg.consys.objects.actors.AkkaReplicaSystem;
import scala.collection.JavaConverters;
import scala.concurrent.JavaConversions;
import scala.concurrent.JavaConversions$;

import java.util.Set;

/**
 * Java wrapper around {@link AkkaReplicaSystem}.
 *
 * @author Mirko Köhler
 */
class JReplicaSystemAkkaImpl implements JReplicaSystem {

	public final AkkaReplicaSystem<String> replicaSystem;

	public JReplicaSystemAkkaImpl(AkkaReplicaSystem<String> replicaSystem) {
		this.replicaSystem = replicaSystem;
	}

	public JReplicaSystemAkkaImpl(ActorSystem actorSystem) {
		this(ReplicaSystems.fromActorSystem(actorSystem));
	}

	public JReplicaSystemAkkaImpl(String hostname, int port) {
		this(ReplicaSystems.fromActorSystem(hostname, port));
	}

	public JReplicaSystemAkkaImpl(int port) {
		this(ReplicaSystems.fromActorSystem(port));
	}

	@Override
	public <T> JRef<T> replicate(String addr, @Local T obj, ConsistencyLevel consistencyLevel) {
		Class<T> objCls = (Class<T>) obj.getClass();
		Ref<String, T> ref = replicaSystem.replicate(addr, obj, objCls, consistencyLevel);

		return new JRefImpl<>(ref);
	}

	@Override
	public <T> JRef<T> replicate(@Local T obj, ConsistencyLevel consistencyLevel) {
		Class<T> objCls = (Class<T>) obj.getClass();
		Ref<String, T> ref = replicaSystem.replicate(obj, objCls, consistencyLevel);

		return new JRefImpl<>(ref);
	}

	@Override
	public <T> JRef<T> lookup(String addr, Class<T> objCls, ConsistencyLevel consistencyLevel) {
		Ref<String, T> ref = replicaSystem.lookup(addr, objCls, consistencyLevel);
		return new JRefImpl<>(ref);
	}

	@Override
	public void delete(String addr) {
		replicaSystem.delete(addr);
	}

	@Override
	public void addReplicaSystem(String hostname, int port) {
		replicaSystem.addOtherReplica(hostname, port);
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
	public boolean equals(Object other) {
		return other instanceof JReplicaSystemAkkaImpl
			&& ((JReplicaSystemAkkaImpl) other).replicaSystem == replicaSystem;
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
