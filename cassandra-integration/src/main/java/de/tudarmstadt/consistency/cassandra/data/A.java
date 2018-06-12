package de.tudarmstadt.consistency.cassandra.data;

import de.tudarmstadt.consistency.cassandra.Main;
import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.store.Handle;

import java.io.Serializable;

/**
 * Created on 12.06.18.
 *
 * @author Mirko Köhler
 */ /*
	Restrict to record syntax.

 */
public class A implements Serializable {
	public final int x;
	public final Handle<@Strong B> b;
	public final String z;

	public @Strong A(int x, Handle<@Strong B> b, String z) {
		this.x = x;
		this.b = b;
		this.z = z;
	}

	public String toString() {
		return String.format("A(x=%s, b=%s, z=%s)", x, b, z);
	}
}
