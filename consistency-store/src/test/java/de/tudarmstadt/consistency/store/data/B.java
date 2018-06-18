package de.tudarmstadt.consistency.store.data;

import java.io.Serializable;
import java.util.Objects;

/**
 * Created on 12.06.18.
 *
 * @author Mirko Köhler
 */
public class B implements Serializable {
	public final String s;

	public B(String s) {
		this.s = s;
	}

	public String toString() {
		return "B(s=" + s + ")";
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof B) {
			B other = (B) obj;
			return Objects.equals(s, other.s);
		}
		return false;
	}
}
