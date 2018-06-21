package de.tudarmstadt.consistency.store.cassandra;

import de.tudarmstadt.consistency.checker.qual.Local;
import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.store.Store;
import de.tudarmstadt.consistency.store.data.A;
import de.tudarmstadt.consistency.store.data.B;
import org.junit.AfterClass;
import org.junit.BeforeClass;
import org.junit.Test;

import java.util.UUID;

import static org.junit.Assert.assertEquals;

/**
 * Created on 18.06.18.
 *
 * @author Mirko Köhler
 */
public class CassandraStoreTest extends ReadWriteStoreTest<UUID, CassandraTransactionContext> {


	private static CassandraDatabase database = null;

	@BeforeClass
	public static void setup() {
		 database = CassandraDatabase.local();
	}

	@AfterClass
	public static void finish() {
		database.close();
	}


	@Override
	Store<UUID, CassandraTransactionContext> store() {
		return database;
	}

	UUID keyA1() {
		return new UUID(573489594L, 8675789563L);
	}

	UUID keyB1() {
		return new UUID(573489456L, 1675789879L);
	}


}
