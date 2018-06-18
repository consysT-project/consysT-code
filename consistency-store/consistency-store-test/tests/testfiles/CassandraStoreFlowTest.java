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
		final Handle<? extends B, StateEvent> b;
		final String z;

		//? extends B is needed as we are not getting a B but, e.g., @Strong B.
		A(int x, Handle<? extends B, StateEvent> b, String z) {
			this.x = x;
			this.b = b;
			this.z = z;
		}

		public String toString() {
			return String.format("A(x=%s, b=%s, z=%s)", x, b, z);
		}
	}

	public static class B implements Serializable {
		final String s;

		B(String s) {
			this.s = s;
		}

		public String toString() {
			return "B(s=" + s + ")";
		}
	}

	public static class O implements Serializable {
		final A a;
		final String s;

		O(A a, String s) {
			this.a = a;
			this.s = s;
		}

		@Override
		public String toString() {
			return "O(A=" + a + ", s=" + s + ")";
		}
	}

	final UUID idA1 = new UUID(573489594L, 8675789563L);
	final UUID idA2 = new UUID(573489456L, 1675789879L);

	final UUID idB1 = new UUID(573489512L, 1675789528L);
	final UUID idB2 = new UUID(573489465L, 1675789841L);

	public void testSetStrong() throws Exception {
		try (CassandraDatabase database = CassandraDatabase.local()) {
			CassandraHandle<@Strong A> strongA1 = (CassandraHandle<@Strong A>) database.obtain(idA1, A.class, Strong.class);
			CassandraHandle<@Strong B> strongB1 = (CassandraHandle<@Strong B>) database.obtain(idB1, B.class, Strong.class);

			strongA1.set(new @Strong A(312, strongB1, "hallo"));
			strongB1.set(new @Strong B(strongA1.get().z));
		}
	}

	public void testSetWeak() throws Exception {
		try (CassandraDatabase database = CassandraDatabase.local()) {
			CassandraHandle<@Weak A> weakA1 = (CassandraHandle<@Weak A>) database.obtain(idA1, A.class, Weak.class);
			CassandraHandle<@Weak B> weakB1 = (CassandraHandle<@Weak B>) database.obtain(idB1, B.class, Weak.class);

			weakA1.set(new @Weak A(312, weakB1, "hallo"));
			weakB1.set(new @Weak B(weakA1.get().z));
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

			A a = new @Strong A(213, weakB,"fire");

			if (weakB.get() == null) {
				// :: error: (invocation.receiver.implicitflow) :: error: (invocation.argument.implicitflow)
				strongA.set(a);
				// :: error: (invocation.receiver.implicitflow) :: error: (invocation.argument.implicitflow)
				strongA.handle(WRITE, a);
			}
		}
	}

	public void testImplicitFlowWithComplexCondition() throws Exception {
		try (CassandraDatabase database = CassandraDatabase.local()) {
			CassandraHandle<@Strong A> strongA = (CassandraHandle<@Strong A>) database.obtain(idA1, A.class, Strong.class);
			CassandraHandle<@Weak B> weakB = (CassandraHandle<@Weak B>) database.obtain(idB1, B.class, Weak.class);

			A a = new @Strong A(213, weakB,"fire");

			B b = weakB.get();

			if (b.s.length() > 3) {
				// :: error: (invocation.receiver.implicitflow) :: error: (invocation.argument.implicitflow)
				strongA.set(a);
				// :: error: (invocation.receiver.implicitflow) :: error: (invocation.argument.implicitflow)
				strongA.handle(WRITE, a);
			}
		}
	}

	public void testCorrectImplicitFlow() throws Exception {
		try (CassandraDatabase database = CassandraDatabase.local()) {
			CassandraHandle<@Strong A> strongA = (CassandraHandle<@Strong A>) database.obtain(idA1, A.class, Strong.class);
			CassandraHandle<@Weak B> weakB = (CassandraHandle<@Weak B>) database.obtain(idB1, B.class, Weak.class);

			B b = new @Weak B("hallo");

			if (strongA.get() == null) {
				weakB.set(b);
				weakB.handle(WRITE, b);
			}
		}
	}



}