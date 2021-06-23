package de.tuda.stg.consys.invariants.subset;

import java.util.function.Supplier;

public class Lazy<T> {
	private Supplier<T> supplier;
	private T cached = null;

	public Lazy(Supplier<T> supplier) {
		if (supplier == null) throw new NullPointerException("supplier was null.");
		this.supplier = supplier;
	}

	public T get() {
		if (supplier != null) {
			synchronized (this) {
				if (supplier != null) {
					cached = supplier.get();
					supplier = null;
				}
			}
		}
		return cached;
	}

	public static <T> Lazy<T> make(Supplier<T> supplier) {
		return new Lazy<T>(supplier);
	}

	@Override
	public String toString() {
		if (cached == null)
			return "lazy val";
		else
			return cached.toString();
	}
}
