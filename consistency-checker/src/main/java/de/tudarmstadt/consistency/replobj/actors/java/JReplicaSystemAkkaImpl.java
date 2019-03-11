package de.tudarmstadt.consistency.replobj.actors.java;

import akka.actor.ActorSystem;
import de.tudarmstadt.consistency.checker.qual.Local;
import de.tudarmstadt.consistency.replobj.Ref;
import de.tudarmstadt.consistency.replobj.ReplicaSystems;
import de.tudarmstadt.consistency.replobj.actors.AkkaReplicaSystem;
import de.tudarmstadt.consistency.replobj.java.JRef;
import de.tudarmstadt.consistency.replobj.java.JReplicaSystem;

/**
 * Created on 01.03.19.
 *
 * @author Mirko Köhler
 */
public class JReplicaSystemAkkaImpl implements JReplicaSystem {

	private final AkkaReplicaSystem<String> replicaSystem;


	public JReplicaSystemAkkaImpl(ActorSystem actorSystem) {
		replicaSystem = ReplicaSystems.fromActorSystem(actorSystem);
	}

	public JReplicaSystemAkkaImpl(int port) {
		replicaSystem = ReplicaSystems.fromActorSystem(port);
	}

	@Override
	public <T> JRef<T> replicate(String addr, @Local T obj, Class<?> consistencyCls) {

		Class<T> objCls = (Class<T>) obj.getClass();
		Ref<String, T, ?> ref = replicaSystem.replicate(addr, obj, objCls, consistencyCls);

		return new JRefImpl<>(ref);
	}

	@Override
	public <T> JRef<T> ref(String addr, Class<T> objCls, Class<?> consistencyCls) {
		Ref<String, T, ?> ref = replicaSystem.ref(addr, objCls, consistencyCls);
		return new JRefImpl<>(ref);
	}

	public void addReplicaSystem(String hostname, int port) {
		replicaSystem.addOtherReplica(hostname, port);
	}
}
