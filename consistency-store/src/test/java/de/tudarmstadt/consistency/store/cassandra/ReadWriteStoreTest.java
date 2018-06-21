package de.tudarmstadt.consistency.store.cassandra;

import de.tudarmstadt.consistency.store.ReferenceService;

/**
 * Created on 18.06.18.
 *
 * @author Mirko Köhler
 */
public abstract class ReadWriteStoreTest<Key, Service extends ReferenceService<Key>> {

//	abstract Store<Key, Service> store();
//
//	abstract Key keyA1();
//	abstract Key keyB1();
//
//
//	@Test
//	public void testPassValueInDatabase() throws Exception {
//		store().commit(service -> {
//			ReadWriteRef<@Strong A, ?> strongA = service.obtain(keyA1(), A.class, Strong.class);
//			ReadWriteRef<@Strong B, ?> strongB = service.obtain(keyB1(), B.class, Strong.class);
//
//			A a = new @Local A(312, strongB, "hallo");
//
//
//			strongA.write(a);
//			A received = strongA.read();
//
//			assertEquals(a, received);
//		}, null);
//	}



}
