package de.tudarmstadt.consistency.demo.data;

import de.tudarmstadt.consistency.store.javaimpl.cassandra.CassandraRef;

import java.io.Serializable;

/**
 * Created on 12.06.18.
 *
 * @author Mirko Köhler
 */
/* Restrict to record syntax. */
public class A implements Serializable {
	private final int x;
	public final CassandraRef<? extends B> b;
	private final String z;

	//? extends B is needed as we are not getting a B but, e.g., @Strong B.
	public A(int x, CassandraRef<? extends B> b, String z) {
		this.x = x;
		this.b = b;
		this.z = z;
	}

	public String toString() {
		return String.format("A(x=%s, b=%s, z=%s)", x, b, z);
	}
}
