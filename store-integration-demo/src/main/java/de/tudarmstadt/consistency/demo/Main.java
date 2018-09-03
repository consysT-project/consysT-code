package de.tudarmstadt.consistency.demo;


import de.tudarmstadt.consistency.checker.qual.Local;
import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.demo.data.A;
import de.tudarmstadt.consistency.demo.data.B;
import de.tudarmstadt.consistency.demo.data.O;
import de.tudarmstadt.consistency.store.javaimpl.cassandra.CassandraDatabase;
import de.tudarmstadt.consistency.store.javaimpl.cassandra.CassandraRef;
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
			UUID id4 = new UUID(573489465L, 1675789841L);

			database.commit(context -> {
				CassandraRef<@Strong A> strongA = context.<@Strong A>obtain(id1, A.class, Strong.class);
				CassandraRef<@Strong B> strongB = context.<@Strong B>obtain(id2, B.class, Strong.class);

				//Types are correct: writing a local value to strong1/2 (strong)
				strongA.write(new @Local A(312, strongB, "hello"));
				strongB.write(new @Local B("world"));

				A aStrong = strongA.read();
				B bStrong = strongB.read();


				Log.info(Main.class, aStrong);
				Log.info(Main.class, bStrong);
				Log.info(Main.class, aStrong.b.read());


				CassandraRef<@Weak B> weakB = context.<@Weak B>obtain(id3, B.class, Weak.class);

				weakB.write(new @Local B("moon"));

				B bWeak = weakB.read();

				//Type clash: writing weak value to strong handle
				//strongB.write(bWeak);


				//Types are correct: writing a strong value to a weak handle
				weakB.write(bStrong);

				//Type clash: Checking implicit flows
				if (weakB.read() == null) {
					//	A a = new @Strong A(213, strong2,"fire");
					//	strong1.write(a);
				}

				CassandraRef<@Strong O> o1 = context.<@Strong O>obtain(id4, O.class, Strong.class);
				o1.write(new @Strong O(new A(31, weakB, "lol"), "rofl"));
				O o = o1.read();

				Log.info(Main.class, o);
				Log.info(Main.class, o.a.b.read());
			}, null);
		}
	}
}
