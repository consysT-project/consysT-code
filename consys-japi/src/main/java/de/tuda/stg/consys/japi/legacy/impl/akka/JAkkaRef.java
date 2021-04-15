package de.tuda.stg.consys.japi.legacy.impl.akka;

import de.tuda.stg.consys.core.legacy.Ref;
import de.tuda.stg.consys.core.legacy.akka.AkkaReplicaSystem;
import de.tuda.stg.consys.japi.legacy.JRef;

import java.io.Serializable;

/**
 * Created on 01.03.19.
 *
 * @author Mirko Köhler
 */
public class JAkkaRef<T> implements JRef<T>, Serializable {

	private final Ref<String, T> ref;

	JAkkaRef(Ref<String, T> ref) {
		this.ref = ref;
	}

	public Ref<String, T> getRef() {
		return ref;
	}

	@Override
	public <R> R getField(String fieldName) {
		return ref.deref().getField(fieldName);
	}

	@Override
	public <R> R setField(String fieldName, R value) {
		ref.deref().setField(fieldName, value);
		return value;
	}

	@Override
	public <R> R invoke(String methodName, Object... args) {
		return ref.deref().invoke(methodName, args);
	}

	@Override
	public void sync() {
		ref.deref().sync();
	}

	@Override
	public void syncAll() {
		ref.deref().syncAll();
	}

	@Override
	public void delete() {
		ref.delete();
	}

	@Override
	public T ref() {
		return ref.ref(); //Throws an exception
	}

	@Override
	public boolean isAvailable() {
		return ref.isAvailable();
	}

	@Override
	public void await() {
		ref.await();
	}

	@Override
	public String addr() {
		return ref.addr();
	}

	@Override
	public void setReplicaSystem(AkkaReplicaSystem replicaSystem) {
		throw new UnsupportedOperationException();
	}

	@Override
	public String toString() {
		return "JRef(" + ref + ")";
	}
}
