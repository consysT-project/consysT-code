package objects.japi;

import de.tuda.stg.consys.objects.Ref;

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
		return ref.deref().getField(fieldName);
	}

	@Override
	public <R> void setField(String fieldName, R value) {
		ref.deref().setField(fieldName, value);
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
	public T ref() {
		return ref.ref(); //Throws an exception
	}

	@Override
	public String addr() {
		return ref.addr();
	}

	@Override
	public String toString() {
		return "JRef(" + ref + ")";
	}


}
