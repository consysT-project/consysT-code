package de.tudarmstadt.consistency.store.cassandra;

import com.datastax.driver.core.ConsistencyLevel;
import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.store.Operation;
import de.tudarmstadt.consistency.store.impl.SerializationRef;

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
public abstract class CassandraRef<V> extends SerializationRef<V> implements Serializable {

	final UUID key;

	//Do not serialize the database, as the corresponding database objects differ on multiple hosts.
	// The database is set to the database object that was used for reading that value.
	private transient CassandraDatabase database;
	
	CassandraRef(UUID key, CassandraDatabase database) {
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
		//Add the current object to the already traversed ones. This avoids an infinite loop in
		//objects that have a reference to each other.
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
			if (fieldType.isAssignableFrom(CassandraRef.class)) {
				((CassandraRef) fieldValue).setDatabase(database);
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
		if (obj instanceof CassandraRef) {
			CassandraRef other = (CassandraRef) obj;
			return Objects.equals(key, other.key) && Objects.equals(database, other.database);
		}

		return false;
	}




	public final static class StrongRef<@Strong V> extends CassandraRef<V> implements Serializable {

		StrongRef(UUID key, CassandraDatabase database) {
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
			return "StrongRef(key=" + key + ")";
		}

		@Override
		public boolean equals(Object obj) {
			if (obj instanceof CassandraRef.StrongRef) {
				return super.equals(obj);
			}

			return false;
		}


	}

	public final static class WeakRef<@Weak V> extends CassandraRef<V> implements Serializable {

		WeakRef(UUID key, CassandraDatabase database) {
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
			return "WeakRef(key=" + key + ")";
		}

		@Override
		public boolean equals(Object obj) {
			if (obj instanceof CassandraRef.WeakRef) {
				return super.equals(obj);
			}

			return false;
		}
	}
}
