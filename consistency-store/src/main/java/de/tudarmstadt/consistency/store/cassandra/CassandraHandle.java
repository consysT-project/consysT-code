package de.tudarmstadt.consistency.store.cassandra;

import com.datastax.driver.core.ConsistencyLevel;
import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.store.Handle;
import de.tudarmstadt.consistency.store.SerializationHandle;
import de.tudarmstadt.consistency.utils.Log;

import java.io.IOException;
import java.io.Serializable;
import java.lang.reflect.Field;
import java.util.UUID;

/**
 * Created on 18.05.18.
 *
 * @author Mirko Köhler
 */
abstract class CassandraHandle<V> extends SerializationHandle<V> implements Serializable {

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
	public V get() throws Exception {
		V result = super.get();
		setDatabaseForHandleFields(result);
		return result;
	}

	private void setDatabaseForHandleFields(Object o) throws IllegalAccessException {
		//If the object contains a handle, set the correct database
		for (Field f : o.getClass().getFields()) {
			Object fieldValue = f.get(o);
			Class<?> fieldType = f.getType();

			if (fieldType.isAssignableFrom(CassandraHandle.class)) {
				((CassandraHandle) fieldValue).setDatabase(database);
			} else if (!fieldType.isPrimitive() && !fieldType.isArray()) {
				setDatabaseForHandleFields(fieldValue);
			}
		}
	}

	@Override
	protected byte[] readBytes() {
		return database.getTable().readWithConsistencyLevelArray(key, getReadConsistencyLevel());
	}

	@Override
	protected void writeBytes(byte[] bytes) {
		database.getTable().writeWithConsistencyLevelArray(key, bytes, getWriteConsistencyLevel());
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
