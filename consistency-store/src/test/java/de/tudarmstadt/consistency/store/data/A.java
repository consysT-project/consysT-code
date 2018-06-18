package de.tudarmstadt.consistency.store.data;

import de.tudarmstadt.consistency.store.Handle;
import de.tudarmstadt.consistency.store.StateEvent;

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
	public final Handle<? extends B, StateEvent> b;
	public final String z;

	//? extends B is needed as we are not getting a B but, e.g., @Strong B.
	public A(int x, Handle<? extends B, StateEvent> b, String z) {
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
