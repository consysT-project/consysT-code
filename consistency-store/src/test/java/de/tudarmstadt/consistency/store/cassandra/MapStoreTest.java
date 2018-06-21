package de.tudarmstadt.consistency.store.cassandra;

import de.tudarmstadt.consistency.checker.qual.Local;
import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.store.Store;
import de.tudarmstadt.consistency.store.data.A;
import de.tudarmstadt.consistency.store.data.B;
import de.tudarmstadt.consistency.store.local.MapRef;
import de.tudarmstadt.consistency.store.local.MapStore;
import de.tudarmstadt.consistency.store.local.MapTransactionContext;
import org.checkerframework.org.objectweb.asm.util.attrs.ASMStackMapTableAttribute;
import org.junit.BeforeClass;
import org.junit.Test;

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
