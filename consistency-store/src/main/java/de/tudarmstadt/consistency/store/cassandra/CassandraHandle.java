package de.tudarmstadt.consistency.store.cassandra;

import com.datastax.driver.core.ConsistencyLevel;
import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.store.SerializationHandle;

import java.io.Serializable;
import java.lang.reflect.Field;
import java.util.UUID;

/**
 * Created on 18.05.18.
 *
 * @author Mirko Köhler
 */
public abstract class CassandraHandle<V> extends SerializationHandle<V> implements Serializable {

	final UUID key;

	//Do not serialize the database, as the corresponding database objects differ on multiple hosts.
	// The database is set to the database object that was used for reading that value.
	private transient CassandraDatabase database;
	
	CassandraHandle(UUID key, CassandraDatabase database) {
		this.key = key;
		this.database = database;
	}

	abstract ConsistencyLevel getReadConsistencyLevel();
	abstract ConsistencyLevel getWriteConsistencyLevel();

	private void setDatabase(CassandraDatabase database) {
		this.database = database;
	}


	@Override
	@SuppressWarnings("unchecked")
	protected V handleRead() throws Exception {
		V result = super.handleRead();
		setDatabaseForHandleFields(result);
		return result;
	}

	private void setDatabaseForHandleFields(Object o) throws IllegalAccessException {
		//If the object contains a handle, set the correct database
		for (Field f : o.getClass().getFields()) {
			Object fieldValue = f.get(o);
			Class<?> fieldType = f.getType();

			//If there is a handle field, then set the database to the current database
			if (fieldType.isAssignableFrom(CassandraHandle.class)) {
				((CassandraHandle) fieldValue).setDatabase(database);

			//Recursively check whether nested classes contain handles
			} else if (!fieldType.isPrimitive() && !fieldType.isArray()) {
				setDatabaseForHandleFields(fieldValue);
			}
		}
	}

	@Override
	protected final byte[] readBytes() {
		return database.getTable().readWithConsistencyLevel(key, getReadConsistencyLevel());
	}

	@Override
	protected final void writeBytes(byte[] bytes) {
		database.getTable().writeWithConsistencyLevel(key, bytes, getWriteConsistencyLevel());
	}


	public final static class StrongHandle<@Strong V> extends CassandraHandle<V> implements Serializable {

		StrongHandle(UUID key, CassandraDatabase database) {
			super(key, database);
		}

		@Override
		final ConsistencyLevel getReadConsistencyLevel() {
			return ConsistencyLevel.ALL;
		}

		@Override
		final ConsistencyLevel getWriteConsistencyLevel() {
			return ConsistencyLevel.ALL;
		}

		@Override
		public String toString() {
			return "StrongHandle(key=" + key + ")";
		}
	}

	public final static class WeakHandle<@Weak V> extends CassandraHandle<V> implements Serializable {

		WeakHandle(UUID key, CassandraDatabase database) {
			super(key, database);
		}

		@Override
		final ConsistencyLevel getReadConsistencyLevel() {
			return ConsistencyLevel.ONE;
		}

		@Override
		final ConsistencyLevel getWriteConsistencyLevel() {
			return ConsistencyLevel.ONE;
		}

		@Override
		public String toString() {
			return "WeakHandle(key=" + key + ")";
		}
	}
}
