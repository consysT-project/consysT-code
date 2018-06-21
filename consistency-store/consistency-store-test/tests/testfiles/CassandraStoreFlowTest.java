import de.tudarmstadt.consistency.checker.qual.Local;
import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.store.cassandra.CassandraDatabase;
import de.tudarmstadt.consistency.store.cassandra.CassandraRef;

import java.io.Serializable;
import java.util.UUID;

class CassandraStoreFlowTest {


	/* Restrict to record syntax. */
	public static class A implements Serializable {
		final int x;
		final CassandraRef<? extends B> b;
		final String z;

		//? extends B is needed as we are not getting a B but, e.g., @Strong B.
		A(int x, CassandraRef<? extends B> b, String z) {
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


	private final UUID idA1 = new UUID(573489594L, 8675789563L);
	private final UUID idA2 = new UUID(573489456L, 1675789879L);

	private final UUID idB1 = new UUID(573489512L, 1675789528L);

	private final CassandraDatabase database = CassandraDatabase.local();

	public void testSetStrong() throws Exception {
		database.commit(service -> {
			CassandraRef<@Strong A> strongA1 = service.obtain(idA1, A.class, Strong.class);
			CassandraRef<@Strong B> strongB1 = service.obtain(idB1, B.class, Strong.class);

			strongA1.write(new @Local A(312, strongB1, "hallo"));
			strongB1.write(new @Local B(strongA1.read().z));
		}, null);
	}

	public void testSetWeak() throws Exception {
		database.commit(service -> {
			CassandraRef<@Weak A> weakA1 = service.obtain(idA1, A.class, Weak.class);
			CassandraRef<@Weak B> weakB1 = service.obtain(idB1, B.class, Weak.class);

			weakA1.write(new @Local A(312, weakB1, "hallo"));
			weakB1.write(new @Local B(weakA1.read().z));
		}, null);
	}

	public void testFlowFromWeakToStrong() throws Exception {
		database.commit(service -> {
			CassandraRef<@Strong A> strongA = service.obtain(idA1, A.class, Strong.class);
			CassandraRef<@Weak A> weakA = service.obtain(idA2, A.class, Weak.class);

			//qq :: error: (argument.type.incompatible)
			//strongA.handle(WRITE, weakA.read());
			// :: error: (argument.type.incompatible)
			strongA.write(weakA.read());

			A a = weakA.read();
			//qq :: error: (argument.type.incompatible)
			//strongA.handle(WRITE, a);
			// :: error: (argument.type.incompatible)
			strongA.write(a);
		}, null);
	}

	public void testFlowFromStrongToWeak() throws Exception {
		database.commit(service -> {
			CassandraRef<@Strong A> strongA = service.obtain(idA1, A.class, Strong.class);
			CassandraRef<@Weak A> weakA = service.obtain(idA2, A.class, Weak.class);

//			weakA.handle(WRITE, strongA.read());
			weakA.write(strongA.read());

			A a = strongA.read();
			//weakA.handle(WRITE, a);
			weakA.write(a);
		}, null);
	}

	public void testImplicitFlowWithSimpleCondition() throws Exception {
		database.commit(service -> {
			CassandraRef<@Strong A> strongA = service.obtain(idA1, A.class, Strong.class);
			CassandraRef<@Weak B> weakB = service.obtain(idB1, B.class, Weak.class);

			A a = new @Local A(213, weakB,"fire");

			if (weakB.read() == null) {
				// :: error: (invocation.receiver.implicitflow)
				strongA.write(a);
				//qq :: error: (invocation.receiver.implicitflow)
				//strongA.handle(WRITE, a);
			}
		}, null);
	}

	public void testImplicitFlowWithComplexCondition() throws Exception {
		database.commit(service -> {
			CassandraRef<@Strong A> strongA = service.obtain(idA1, A.class, Strong.class);
			CassandraRef<@Weak B> weakB = service.obtain(idB1, B.class, Weak.class);


			B b = weakB.read();
			if (b.s.length() > 3) {
				// :: error: (invocation.receiver.implicitflow) :: error: (invocation.argument.implicitflow)
				strongA.write(strongA.read());
				//qq :: error: (invocation.receiver.implicitflow) :: error: (invocation.argument.implicitflow)
				//strongA.handle(WRITE, strongA.read());
			}
		}, null);
	}

	public void testCorrectImplicitFlow() throws Exception {
		database.commit(service -> {
			CassandraRef<@Strong A> strongA = service.obtain(idA1, A.class, Strong.class);
			CassandraRef<@Weak B> weakB = service.obtain(idB1, B.class, Weak.class);

			B b = new @Local B("hallo");

			if (strongA.read() == null) {
				weakB.write(b);
				//weakB.handle(WRITE, b);
			}
		}, null);
	}



}