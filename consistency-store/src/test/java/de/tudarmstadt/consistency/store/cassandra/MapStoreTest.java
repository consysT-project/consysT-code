package de.tudarmstadt.consistency.store.cassandra;

import de.tudarmstadt.consistency.store.Store;
import de.tudarmstadt.consistency.store.local.MapStore;
import de.tudarmstadt.consistency.store.local.MapTransactionContext;
import org.junit.BeforeClass;

import static org.junit.Assert.assertEquals;

/**
 * Created on 18.06.18.
 *
 * @author Mirko Köhler
 */
public class MapStoreTest extends ReadWriteStoreTest<Object, MapTransactionContext> {


	private static MapStore database = null;

	@BeforeClass
	public static void setup() {
		 database = MapStore.create();
	}


	@Override
	Store<Object, MapTransactionContext> store() {
		return database;
	}

	Object keyA1() {
		return 1;
	}

	Object keyB1() {
		return 2;
	}



}
