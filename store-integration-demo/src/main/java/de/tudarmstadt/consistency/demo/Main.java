package de.tudarmstadt.consistency.demo;


import de.tudarmstadt.consistency.demo.data.A;
import de.tudarmstadt.consistency.demo.data.B;
import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.store.Handle;
import de.tudarmstadt.consistency.store.cassandra.CassandraDatabase;
import de.tudarmstadt.consistency.utils.Log;

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


			/*
			TODO: When using a class as valueClass argument (e.g. A.class) then the annotated type parameter does not work

			In that case only a cast works, i.e.
			Handle<@Strong A>) database.obtain(id1, A.class, Strong.class)

			Is there a better way to handle that? In the current implementation the value class
			argument is not needed.
			 */
			Handle<@Strong A> strong1 = database.<@Strong A>obtain(id1, null, Strong.class);
			//B.class returns @Inconsistent Class<@Inconsistent B>, but obtain requires @Inconsistent Class<@Strong B>
			Handle<@Strong B> strong2 = (Handle<@Strong B>) database.obtain(id2, B.class, Strong.class);

			//Types are correct: writing a local value to strong1/2 (strong)
			strong1.set(new @Strong A(312, strong2, "hallo"));
			strong2.set(new @Strong B("welt"));

			A aStrong = strong1.get();
			B bStrong = strong2.get();


			Log.info(Main.class, aStrong);
			Log.info(Main.class, bStrong);
			Log.info(Main.class, aStrong.b.get());


			Handle<@Weak B> weak1 = (Handle<@Weak B>) database.obtain(id3, B.class, Weak.class);

			weak1.set(new @Weak B("gude"));

			B bWeak = weak1.get();

			//Type clash: writing weak value to strong handle
			strong2.set(bWeak);

			//Types are correct: writing a strong value to a weak handle
			weak1.set(bStrong);

			//Type clash: Checking implicit flows
			if (weak1.get() == null) {
				strong1.set(new @Strong A(213, strong2,"fire"));
			}

		}
	}
}
