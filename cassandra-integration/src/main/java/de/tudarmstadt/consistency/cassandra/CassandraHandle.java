package de.tudarmstadt.consistency.cassandra;

import com.datastax.driver.core.ConsistencyLevel;
import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.store.Handle;
import de.tudarmstadt.consistency.store.impl.SerializerHandle;
import de.tudarmstadt.consistency.store.utils.Log;

import java.io.IOException;
import java.io.Serializable;
import java.util.UUID;

/**
 * Created on 18.05.18.
 *
 * @author Mirko Köhler
 */
abstract class CassandraHandle<V> implements Handle<V>, Serializable {

	protected final UUID key;

	//Do not serialize the database. The database is set to the database object that was used for reading
	//that value.
	private transient CassandraDatabase database;
	
	CassandraHandle(UUID key, CassandraDatabase database) {
		this.key = key;
		this.database = database;
	}

	abstract ConsistencyLevel getReadConsistencyLevel();
	abstract ConsistencyLevel getWriteConsistencyLevel();

	void setDatabase(CassandraDatabase database) {
		this.database = database;
	}


	@Override
	@SuppressWarnings("unchecked")
	public V get() {
		V result = (V) database.getTable().readWithConsistencyLevel(key, getReadConsistencyLevel());
		Log.info(CassandraHandle.class, "Reading <" + result + "> with " + getReadConsistencyLevel());
		return result;
	}

	@Override
	public void set(V value) {
		Log.info(CassandraHandle.class, "Writing <" + value + "> with " + getReadConsistencyLevel());
		database.getTable().writeWithConsistencyLevel(key, value, getWriteConsistencyLevel());
	}

	public static class StrongHandle<@Strong V> extends CassandraHandle<V> implements Serializable {

		StrongHandle(UUID key, CassandraDatabase database) {
			super(key, database);
		}

		@Override
		ConsistencyLevel getReadConsistencyLevel() {
			return ConsistencyLevel.ALL;
		}

		@Override
		ConsistencyLevel getWriteConsistencyLevel() {
			return ConsistencyLevel.ALL;
		}

		@Override
		public String toString() {
			return "StrongHandle(key=" + key + ")";
		}
	}

	public static class WeakHandle<@Weak V> extends CassandraHandle<V> implements Serializable {

		WeakHandle(UUID key, CassandraDatabase database) {
			super(key, database);
		}

		@Override
		ConsistencyLevel getReadConsistencyLevel() {
			return ConsistencyLevel.ONE;
		}

		@Override
		ConsistencyLevel getWriteConsistencyLevel() {
			return ConsistencyLevel.ONE;
		}

		@Override
		public String toString() {
			return "WeakHandle(key=" + key + ")";
		}
	}
}
