package de.tudarmstadt.consistency.cassandra.data;

import de.tudarmstadt.consistency.checker.qual.Strong;

import java.io.Serializable;

/**
 * Created on 12.06.18.
 *
 * @author Mirko Köhler
 */
public class B implements Serializable {
	public final String s;

	public @Strong B(String s) {
		this.s = s;
	}

	public String toString() {
		return "B(s=" + s + ")";
	}
}
