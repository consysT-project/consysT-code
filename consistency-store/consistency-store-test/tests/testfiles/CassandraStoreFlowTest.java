import de.tudarmstadt.consistency.checker.qual.Local;
import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.store.Handle;
import de.tudarmstadt.consistency.store.StateEvent;
import de.tudarmstadt.consistency.store.cassandra.CassandraDatabase;
import de.tudarmstadt.consistency.store.cassandra.CassandraHandle;

import java.io.Serializable;
import java.util.UUID;

import static de.tudarmstadt.consistency.store.StateEvent.READ;
import static de.tudarmstadt.consistency.store.StateEvent.WRITE;

class CassandraStoreFlowTest {


	/* Restrict to record syntax. */
	public static class A implements Serializable {
		final int x;
		final CassandraHandle<? extends B> b;
		final String z;

		//? extends B is needed as we are not getting a B but, e.g., @Strong B.
		A(int x, CassandraHandle<? extends B> b, String z) {
			this.x = x;
			this.b = b;
			this.z = z;
		}

	}

	public static class B implements Serializable {
		final String s;

		B(String s) {
			this.s = s;
		}
	}


	final UUID idA1 = new UUID(573489594L, 8675789563L);
	final UUID idA2 = new UUID(573489456L, 1675789879L);

	final UUID idB1 = new UUID(573489512L, 1675789528L);

	public void testSetStrong() throws Exception {
		try (CassandraDatabase database = CassandraDatabase.local()) {
			CassandraHandle<@Strong A> strongA1 = (CassandraHandle<@Strong A>) database.obtain(idA1, A.class, Strong.class);
			CassandraHandle<@Strong B> strongB1 = (CassandraHandle<@Strong B>) database.obtain(idB1, B.class, Strong.class);

			strongA1.set(new @Local A(312, strongB1, "hallo"));
			strongB1.set(new @Local B(strongA1.get().z));
		}
	}

	public void testSetWeak() throws Exception {
		try (CassandraDatabase database = CassandraDatabase.local()) {
			CassandraHandle<@Weak A> weakA1 = (CassandraHandle<@Weak A>) database.obtain(idA1, A.class, Weak.class);
			CassandraHandle<@Weak B> weakB1 = (CassandraHandle<@Weak B>) database.obtain(idB1, B.class, Weak.class);

			weakA1.set(new @Local A(312, weakB1, "hallo"));
			weakB1.set(new @Local B(weakA1.get().z));
		}
	}

	public void testFlowFromWeakToStrong() throws Exception {
		try (CassandraDatabase database = CassandraDatabase.local()) {
			CassandraHandle<@Strong A> strongA = (CassandraHandle<@Strong A>) database.obtain(idA1, A.class, Strong.class);
			CassandraHandle<@Weak A> weakA = (CassandraHandle<@Weak A>) database.obtain(idA2, A.class, Weak.class);

			// :: error: (argument.type.incompatible)
			strongA.handle(WRITE, weakA.get());
			// :: error: (argument.type.incompatible)
			strongA.set(weakA.get());

			A a = weakA.get();
			// :: error: (argument.type.incompatible)
			strongA.handle(WRITE, a);
			// :: error: (argument.type.incompatible)
			strongA.set(a);
		}
	}

	public void testFlowFromStrongToWeak() throws Exception {
		try (CassandraDatabase database = CassandraDatabase.local()) {
			CassandraHandle<@Strong A> strongA = (CassandraHandle<@Strong A>) database.obtain(idA1, A.class, Strong.class);
			CassandraHandle<@Weak A> weakA = (CassandraHandle<@Weak A>) database.obtain(idA2, A.class, Weak.class);

			weakA.handle(WRITE, strongA.get());
			weakA.set(strongA.get());

			A a = strongA.get();
			weakA.handle(WRITE, a);
			weakA.set(a);
		}
	}

	public void testImplicitFlowWithSimpleCondition() throws Exception {
		try (CassandraDatabase database = CassandraDatabase.local()) {
			CassandraHandle<@Strong A> strongA = (CassandraHandle<@Strong A>) database.obtain(idA1, A.class, Strong.class);
			CassandraHandle<@Weak B> weakB = (CassandraHandle<@Weak B>) database.obtain(idB1, B.class, Weak.class);

			A a = new @Local A(213, weakB,"fire");

			if (weakB.get() == null) {
				// :: error: (invocation.receiver.implicitflow)
				strongA.set(a);
				// :: error: (invocation.receiver.implicitflow)
				strongA.handle(WRITE, a);
			}
		}
	}

	public void testImplicitFlowWithComplexCondition() throws Exception {
		try (CassandraDatabase database = CassandraDatabase.local()) {
			CassandraHandle<@Strong A> strongA = (CassandraHandle<@Strong A>) database.obtain(idA1, A.class, Strong.class);
			CassandraHandle<@Weak B> weakB = (CassandraHandle<@Weak B>) database.obtain(idB1, B.class, Weak.class);


			B b = weakB.get();
			if (b.s.length() > 3) {
				// :: error: (invocation.receiver.implicitflow) :: error: (invocation.argument.implicitflow)
				strongA.set(strongA.get());
				// :: error: (invocation.receiver.implicitflow) :: error: (invocation.argument.implicitflow)
				strongA.handle(WRITE, strongA.get());
			}
		}
	}

	public void testCorrectImplicitFlow() throws Exception {
		try (CassandraDatabase database = CassandraDatabase.local()) {
			CassandraHandle<@Strong A> strongA = (CassandraHandle<@Strong A>) database.obtain(idA1, A.class, Strong.class);
			CassandraHandle<@Weak B> weakB = (CassandraHandle<@Weak B>) database.obtain(idB1, B.class, Weak.class);

			B b = new @Local B("hallo");

			if (strongA.get() == null) {
				weakB.set(b);
				weakB.handle(WRITE, b);
			}
		}
	}



}