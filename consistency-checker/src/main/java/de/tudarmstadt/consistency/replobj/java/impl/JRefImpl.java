package de.tudarmstadt.consistency.replobj.java.impl;

import de.tudarmstadt.consistency.replobj.Ref;
import de.tudarmstadt.consistency.replobj.actors.ActorReplicaSystem;
import de.tudarmstadt.consistency.replobj.java.JRef;

/**
 * Created on 01.03.19.
 *
 * @author Mirko Köhler
 */
public class JRefImpl<T> implements JRef<T> {

	private final Ref<String, T,?> ref;

	public JRefImpl(Ref<String, T,?> ref) {
		this.ref = ref;
	}

	public JRefImpl(String addr, ActorReplicaSystem<String> replicaSystem, Class<?> consistencyCls) {
		this.ref = ActorReplicaSystem.RefImpl$.MODULE$.<String, T, Object>create(addr, replicaSystem, (Class<Object>) consistencyCls);
	}

	@Override
	public <R> R getField(String fieldName) {
		return ref.toReplicatedObject().getField(fieldName);
	}

	@Override
	public <R> void setField(String fieldName, R value) {
		ref.toReplicatedObject().setField(fieldName, value);
	}

	@Override
	public <R> R invoke(String methodName, Object... args) {
		return ref.toReplicatedObject().invoke(methodName, args);
	}

	@Override
	public void synchronize() {
		ref.toReplicatedObject().sync();
	}

	@Override
	public T remote() {
		return ref.remote(); //Throws an exception
	}


}
