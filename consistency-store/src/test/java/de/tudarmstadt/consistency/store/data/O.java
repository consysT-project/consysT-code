package de.tudarmstadt.consistency.store.data;

import java.io.Serializable;
import java.util.Objects;

/**
 * Created on 18.06.18.
 *
 * @author Mirko Köhler
 */
public class O implements Serializable {

	public final A a;
	public final String s;

	public O(A a, String s) {
		this.a = a;
		this.s = s;
	}

	@Override
	public String toString() {
		return "O(A=" + a + ", s=" + s + ")";
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof O) {
			O other = (O) obj;
			return Objects.equals(a, other.a) && Objects.equals(s, other.s);
		}
		return false;
	}
}
