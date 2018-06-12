package de.tudarmstadt.consistency.cassandra;


import de.tudarmstadt.consistency.cassandra.data.A;
import de.tudarmstadt.consistency.cassandra.data.B;
import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
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
			UUID id3 = new UUID(573489456L, 1675789879L);


			Handle<@Strong A> strong1 = (Handle<@Strong A>) database.obtain(id1, A.class, Strong.class);
			Handle<@Strong B> strong2 = (Handle<@Strong B>) database.obtain(id2, B.class, Strong.class);

			//Types are correct: writing a local value to strong1/2 (strong)
			strong1.set(new A(312, strong2, "hallo"));
			strong2.set(new B("welt"));

			A aStrong = strong1.get();
			B bStrong = strong2.get();

			Log.info(Main.class, aStrong);
			Log.info(Main.class, bStrong);

			Log.info(Main.class, aStrong.b.get());


			Handle<@Weak B> weak1 = (Handle<@Weak B>) database.obtain(id3, B.class, Weak.class);

			weak1.set(new B("gude"));

			B bWeak = weak1.get();

			//Types are incorrect: writing weak value to strong handle
	//		strong2.set(bWeak);

			//Types are correct: writing a strong value to a weak handle
			weak1.set(bStrong);

			//Type clash: Checking implicit flows
			if (weak1.get() == null) {
				//strong1.set(new A(213, strong2,"fire"));
			}

		}
	}
}
