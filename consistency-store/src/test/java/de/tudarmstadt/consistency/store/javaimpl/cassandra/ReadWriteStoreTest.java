package de.tudarmstadt.consistency.store.javaimpl.cassandra;

import de.tudarmstadt.consistency.checker.qual.Local;
import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.store.javaimpl.TransactionContext;
import de.tudarmstadt.consistency.store.javaimpl.Store;
import de.tudarmstadt.consistency.store.javaimpl.data.A;
import de.tudarmstadt.consistency.store.javaimpl.data.B;
import de.tudarmstadt.consistency.store.javaimpl.impl.ReadWriteRef;
import org.junit.Assert;
import org.junit.Test;

import static junit.framework.TestCase.assertEquals;

/**
 * Created on 18.06.18.
 *
 * @author Mirko Köhler
 */
public abstract class ReadWriteStoreTest<Key, Service extends TransactionContext<Key>> {

	abstract Store<Key, Service> store();

	abstract Key keyA1();
	abstract Key keyB1();


	@Test
	public void testPassStrongValueInDatabase() throws Exception {
		store().commit(service -> {
			//TODO: Specify that service returns a special Ref and not the general Ref.
			ReadWriteRef<@Strong A> strongA = (ReadWriteRef<@Strong A>) service.<@Strong A>obtain(keyA1(), A.class, Strong.class);
			ReadWriteRef<@Strong B> strongB = (ReadWriteRef<@Strong B>) service.<@Strong B>obtain(keyB1(), B.class, Strong.class);

			A a = new @Local A(312, strongB, "hallo");


			strongA.write(a);
			A received = strongA.read();

			assertEquals(a, received);
		}, null);
	}


	@Test
	public void testUseStrongStoredReference() throws Exception {
		store().commit(service -> {
			ReadWriteRef<@Strong A> strongA = (ReadWriteRef<@Strong A>) service.<@Strong A>obtain(keyA1(), A.class, Strong.class);
			ReadWriteRef<@Strong B> strongB = (ReadWriteRef<@Strong B>) service.<@Strong B>obtain(keyB1(), B.class, Strong.class);

			A a = new @Local A(4382, strongB, "hallo2");
			B b = new @Local B("test1");

			strongA.write(a);
			strongB.write(b);

			B received1 = strongA.read().b.read();
			B received2 = strongB.read();

			Assert.assertEquals(b, received1);
			Assert.assertEquals(b, received2);
		}, null);
	}

	@Test
	public void testPassWeakValueInDatabase() throws Exception {
		store().commit(service -> {
			//TODO: Specify that service returns a special Ref and not the general Ref.
			ReadWriteRef<@Weak A> strongA = (ReadWriteRef<@Weak A>) service.<@Weak A>obtain(keyA1(), A.class, Weak.class);
			ReadWriteRef<@Weak B> strongB = (ReadWriteRef<@Weak B>) service.<@Weak B>obtain(keyB1(), B.class, Weak.class);

			A a = new @Local A(312, strongB, "hallo");


			strongA.write(a);
			A received = strongA.read();

			assertEquals(a, received);
		}, null);
	}


	@Test
	public void testUseWeakStoredReference() throws Exception {
		store().commit(service -> {
			ReadWriteRef<@Weak A> strongA = (ReadWriteRef<@Weak A>) service.<@Weak A>obtain(keyA1(), A.class, Weak.class);
			ReadWriteRef<@Weak B> strongB = (ReadWriteRef<@Weak B>) service.<@Weak B>obtain(keyB1(), B.class, Weak.class);

			A a = new @Local A(4382, strongB, "hallo2");
			B b = new @Local B("test1");

			strongA.write(a);
			strongB.write(b);

			B received1 = strongA.read().b.read();
			B received2 = strongB.read();

			Assert.assertEquals(b, received1);
			Assert.assertEquals(b, received2);
		}, null);
	}

}
