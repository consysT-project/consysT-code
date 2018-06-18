package de.tudarmstadt.consistency.demo.data;

import java.io.Serializable;

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
}
