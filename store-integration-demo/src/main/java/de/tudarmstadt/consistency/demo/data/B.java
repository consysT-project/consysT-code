package de.tudarmstadt.consistency.demo.data;

import java.io.Serializable;

/**
 * Created on 12.06.18.
 *
 * @author Mirko Köhler
 */
public class B implements Serializable {
	private final String s;

	public B(String s) {
		this.s = s;
	}

	public String toString() {
		return "B(s=" + s + ")";
	}
}
