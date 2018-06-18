package de.tudarmstadt.consistency.store.cassandra;

import com.datastax.driver.core.ConsistencyLevel;
import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.store.SerializationHandle;

import java.io.Serializable;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.HashSet;
import java.util.Objects;
import java.util.Set;
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
	transient CassandraDatabase database;
	
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
		setDatabaseForHandleFields(result, new HashSet<>());
		return result;
	}

	private void setDatabaseForHandleFields(Object o, Set<Object> alreadyTraversed) throws IllegalAccessException {
		alreadyTraversed.add(o);

		//If the object contains a handle, set the correct database
		for (Field f : o.getClass().getFields()) {
			Object fieldValue = f.get(o);
			Class<?> fieldType = f.getType();

			//Skip static fields
			//TODO: Is this sufficient?
			if (Modifier.isStatic(f.getModifiers())) {
				continue;
			}

			//If there is a handle field, then set the database to the current database
			if (fieldType.isAssignableFrom(CassandraHandle.class)) {
				((CassandraHandle) fieldValue).setDatabase(database);
			}

			//Recursively check whether nested classes contain handles
			if (!alreadyTraversed.contains(fieldValue)) {
				setDatabaseForHandleFields(fieldValue, alreadyTraversed);
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


	@Override
	public boolean equals(Object obj) {
		if (obj instanceof CassandraHandle) {
			CassandraHandle other = (CassandraHandle) obj;
			return Objects.equals(key, other.key) && Objects.equals(database, other.database);
		}

		return false;
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

		@Override
		public boolean equals(Object obj) {
			if (obj instanceof StrongHandle) {
				return super.equals(obj);
			}

			return false;
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

		@Override
		public boolean equals(Object obj) {
			if (obj instanceof WeakHandle) {
				return super.equals(obj);
			}

			return false;
		}
	}
}
