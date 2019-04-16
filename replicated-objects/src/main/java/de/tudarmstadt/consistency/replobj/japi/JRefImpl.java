package de.tudarmstadt.consistency.replobj.japi;

import de.tudarmstadt.consistency.replobj.Ref;

import java.io.Serializable;

/**
 * Created on 01.03.19.
 *
 * @author Mirko Köhler
 */
public class JRefImpl<T> implements JRef<T>, Serializable {

	private final Ref<String, T> ref;

	JRefImpl(Ref<String, T> ref) {
		this.ref = ref;
	}

	public Ref<String, T> getRef() {
		return ref;
	}

	@Override
	public <R> R getField(String fieldName) {
		return ref.lookupObject().getField(fieldName);
	}

	@Override
	public <R> void setField(String fieldName, R value) {
		ref.lookupObject().setField(fieldName, value);
	}

	@Override
	public <R> R invoke(String methodName, Object... args) {
		return ref.lookupObject().invoke(methodName, args);
	}

	@Override
	public void sync() {
		ref.lookupObject().sync();
	}

	@Override
	public void syncAll() {
		ref.lookupObject().syncAll();
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
