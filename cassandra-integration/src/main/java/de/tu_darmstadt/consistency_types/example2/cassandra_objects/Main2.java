package de.tu_darmstadt.consistency_types.example2.cassandra_objects;

import de.tu_darmstadt.consistency_types.checker.qual.Strong;
import de.tu_darmstadt.consistency_types.store.Handle;
import de.tu_darmstadt.consistency_types.store.utils.Log;

import java.util.UUID;

/**
 * Created on 29.05.18.
 *
 * @author Mirko Köhler
 */
public class Main2 {

	/*
		Restrict to record syntax.

	 */
	public static class A {
		public final int x;
		public final Handle<@Strong B> b;
		public final String z;

		public @Strong A(int x, Handle<@Strong B> b, String z) {
			this.x = x;
			this.b = b;
			this.z = z;
		}
	}

	public static class B {
		public final String s;

		public @Strong B(String s) {
			this.s = s;
		}

		public String toString() {
			return "B(s=" + s + ")";
		}
	}

	public static void main(String... args) throws Exception {
		try (CassandraDatabase database = CassandraDatabase.local()) {

			UUID id1 = new UUID(573489594L, 8675789563L);
			UUID id2 = new UUID(573489512L, 1675789528L);

			Handle<@Strong A> handle1 = (Handle<@Strong A>) database.obtain(id1, A.class, Strong.class);
			Handle<@Strong B> handle2 = (Handle<@Strong B>) database.obtain(id2, B.class, Strong.class);


			handle1.set(new A(312, handle2, "hallo"));
			handle2.set(new B("welt"));
			Log.info(Main2.class, handle2.get());
		}
	}
}
