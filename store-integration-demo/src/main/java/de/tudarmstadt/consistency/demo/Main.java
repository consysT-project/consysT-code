package de.tudarmstadt.consistency.demo;


import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.demo.data.A;
import de.tudarmstadt.consistency.demo.data.B;
import de.tudarmstadt.consistency.demo.data.O;
import de.tudarmstadt.consistency.store.cassandra.CassandraDatabase;
import de.tudarmstadt.consistency.store.cassandra.CassandraRef;
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

			database.commit(service -> {
				/*
			TODO: When using a class as valueClass argument (e.g. A.class) then the annotated type parameter does not work

			In that case only a cast works, i.e.
			Ref<@Strong A>) database.obtain(id1, A.class, Strong.class)

			Is there a better way to handle that? In the current implementation the value class
			argument is not needed.
			 */
				CassandraRef<@Strong A> strong1 = service.obtain(id1, A.class, Strong.class);
				//B.class returns @Inconsistent Class<@Inconsistent B>, but obtain requires @Inconsistent Class<@Strong B>
				CassandraRef<@Strong B> strong2 = service.obtain(id2, B.class, Strong.class);

				//Types are correct: writing a local value to strong1/2 (strong)
				strong1.write(new @Strong A(312, strong2, "hallo"));
				strong2.write(new @Strong B("welt"));

				A aStrong = strong1.read();
				B bStrong = strong2.read();


				Log.info(Main.class, aStrong);
				Log.info(Main.class, bStrong);
				Log.info(Main.class, aStrong.b.read());


				CassandraRef<@Weak B> weak1 = service.obtain(id3, B.class, Weak.class);

				weak1.write(new @Weak B("gude"));

				B bWeak = weak1.read();

				//Type clash: writing weak value to strong handle
				//strong2.write(bWeak);
				//strong2.handle(WRITE, bWeak);


				//Types are correct: writing a strong value to a weak handle
				weak1.write(bStrong);

				//Type clash: Checking implicit flows
				if (weak1.read() == null) {
					//	A a = new @Strong A(213, strong2,"fire");
					//	strong1.write(a);
					//	strong1.handle(WRITE, a);
				}

				CassandraRef<@Strong O> o1 = service.obtain(id4, null, Strong.class);
				o1.write(new @Strong O(new A(31, weak1, "lol"), "rofl"));
				O o = o1.read();

				Log.info(Main.class, o);
				Log.info(Main.class, o.a.b.read());
			}, null);



		}
	}
}
