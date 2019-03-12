package de.tudarmstadt.consistency.replobj.actors.java;

import de.tudarmstadt.consistency.replobj.Ref;
import de.tudarmstadt.consistency.replobj.java.JRef;

import java.io.Serializable;

/**
 * Created on 01.03.19.
 *
 * @author Mirko Köhler
 */
public class JRefImpl<T> implements JRef<T>, Serializable {

	private final Ref<String, T,?> ref;

	JRefImpl(Ref<String, T,?> ref) {
		this.ref = ref;
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
	public void sync() {
		ref.toReplicatedObject().sync();
	}

	@Override
	public T remote() {
		return ref.remote(); //Throws an exception
	}

	@Override
	public String toString() {
		return "JRef(" + ref + ")";
	}


}
