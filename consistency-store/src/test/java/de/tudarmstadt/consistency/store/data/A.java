package de.tudarmstadt.consistency.store.data;

import de.tudarmstadt.consistency.store.impl.ReadWriteRef;

import java.io.Serializable;
import java.util.Objects;

/**
 * Created on 12.06.18.
 *
 * @author Mirko Köhler
 */
/* Restrict to record syntax. */
public class A implements Serializable {
	public final int x;
	public final ReadWriteRef<? extends B> b;
	public final String z;

	//? extends B is needed as we are not getting a B but, e.g., @Strong B.
	public A(int x, ReadWriteRef<? extends B> b, String z) {
		this.x = x;
		this.b = b;
		this.z = z;
	}

	public String toString() {
		return String.format("A(x=%s, b=%s, z=%s)", x, b, z);
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof A) {
			A other = (A) obj;
			return x == other.x && Objects.equals(b, other.b) && Objects.equals(z, other.z);
		}
		return false;
	}
}
