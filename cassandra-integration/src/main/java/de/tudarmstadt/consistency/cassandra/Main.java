package de.tudarmstadt.consistency.cassandra;


import de.tudarmstadt.consistency.cassandra.data.A;
import de.tudarmstadt.consistency.cassandra.data.B;
import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.store.Handle;
import de.tudarmstadt.consistency.store.utils.Log;

import java.util.UUID;

/**
 * Created on 29.05.18.
 *
 * @author Mirko Köhler
 */
public class Main {

	public static void main(String... args) throws Exception {
		try (CassandraDatabase database = CassandraDatabase.local()) {

			UUID id1 = new UUID(573489594L, 8675789563L);
			UUID id2 = new UUID(573489512L, 1675789528L);

			Handle<@Strong A> handle1 = (Handle<@Strong A>) database.obtain(id1, A.class, Strong.class);
			Handle<@Strong B> handle2 = (Handle<@Strong B>) database.obtain(id2, B.class, Strong.class);


			handle1.set(new A(312, handle2, "hallo"));
			handle2.set(new B("welt"));

			A a = handle1.get();
			B b = handle2.get();

			Log.info(Main.class, a);
			Log.info(Main.class, b);

			Log.info(Main.class, a.b.get());
		}
	}
}
