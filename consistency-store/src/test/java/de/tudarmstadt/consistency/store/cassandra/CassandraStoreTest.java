package de.tudarmstadt.consistency.store.cassandra;

import de.tudarmstadt.consistency.checker.qual.Local;
import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.store.data.A;
import de.tudarmstadt.consistency.store.data.B;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;

import java.util.UUID;

import static de.tudarmstadt.consistency.store.StateEvent.READ;
import static org.junit.Assert.assertEquals;

/**
 * Created on 18.06.18.
 *
 * @author Mirko Köhler
 */
public class CassandraStoreTest {

	/*
	TODO: When using a class as valueClass argument (e.g. A.class) then the annotated type parameter does not work

	In that case only a cast works, i.e.
	Handle<@Strong A>) database.obtain(id1, A.class, Strong.class)

	Is there a better way to handle that? In the current implementation the value class
	argument is not needed.

	CassandraHandle<@Strong A> strong1 = database.<@Strong A>obtain(id1, null, Strong.class);
	//B.class returns @Inconsistent Class<@Inconsistent B>, but obtain requires @Inconsistent Class<@Strong B>
	CassandraHandle<@Strong B> strong2 = (CassandraHandle<@Strong B>) database.obtain(id2, B.class, Strong.class);
	*/


	UUID idA1 = new UUID(573489594L, 8675789563L);
	UUID idA2 = new UUID(573489512L, 1675789528L);
	UUID idB1 = new UUID(573489456L, 1675789879L);
	UUID idB2 = new UUID(573489465L, 1675789841L);

	static CassandraDatabase database = null;

	@BeforeClass
	public static void setup() {
		 database = CassandraDatabase.local();
	}

	@AfterClass
	public static void finish() {
		database.close();
	}


	@Test
	public void testPassValueInDatabase() throws Exception {
		database.commit(service -> {
			CassandraHandle<@Strong A> strongA = service.<@Strong A>obtain(idA1, A.class, Strong.class);
			CassandraHandle<@Strong B> strongB = service.<@Strong B>obtain(idB1, B.class, Strong.class);

			A a = new @Local A(312, strongB, "hallo");

			strongA.set(a);
			A received = strongA.get();

			assertEquals(a, received);
		}, null);
	}

	@Test
	public void testUseLocalReference() throws Exception {
		database.commit(service -> {
			CassandraHandle<@Strong A> strongA = service.<@Strong A>obtain(idA1, A.class, Strong.class);
			CassandraHandle<@Strong B> strongB = service.<@Strong B>obtain(idB1, B.class, Strong.class);

			A a = new @Local A(4382, strongB, "hallo2");
			B b = new @Local B("test1");

			strongA.set(a);
			strongB.set(b);

			B received1 = strongA.get().b.handle(READ);
			B received2 = strongB.get();

			assertEquals(b, received1);
			assertEquals(b, received2);
		}, null);
	}

}
