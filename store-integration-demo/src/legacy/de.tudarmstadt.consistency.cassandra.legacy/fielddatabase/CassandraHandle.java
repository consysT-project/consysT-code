package de.tudarmstadt.consistency.demo.legacy.fielddatabase;

import com.datastax.driver.core.ConsistencyLevel;
import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.store.Handle;
import de.tudarmstadt.consistency.store.utils.Log;

import java.io.IOException;
import java.util.UUID;

/**
 * Created on 18.05.18.
 *
 * @author Mirko Köhler
 */
abstract class CassandraHandle<V> implements Handle<V> {

	private final CassandraDatabase database;

	private final UUID key;
	private final CassandraDatabase.ObjectTable<V> table;
	private final Class<V> valueType;

	CassandraHandle(CassandraDatabase database, CassandraDatabase.ObjectTable<V> table, UUID key, Class<V> valueType) {
		this.database = database;
		this.key = key;
		this.table = table;
		this.valueType = valueType;
	}

	abstract ConsistencyLevel getReadConsistencyLevel();
	abstract ConsistencyLevel getWriteConsistencyLevel();


	protected UUID getKey() {
		return key;
	}

	protected Class<V> getValueType() {
		return valueType;
	}


	@Override
	public V get() throws IOException, ClassNotFoundException {
		V result = table.select(key, getReadConsistencyLevel());
		Log.info(CassandraHandle.class, "Reading <" + result + "> with " + getReadConsistencyLevel());
		return result;
	}


	@Override
	public void set(V value) throws IOException {
		table.insertInto(getKey(), value, getWriteConsistencyLevel());

		Log.info(CassandraHandle.class, "Writing <" + value + "> with " + getWriteConsistencyLevel());
	}


	static class StrongHandle<@Strong V> extends CassandraHandle<V> {

		StrongHandle(CassandraDatabase database, CassandraDatabase.ObjectTable<V> table, UUID key, Class<V> clazz) {
			super(database, table, key, clazz);
		}

		@Override
		ConsistencyLevel getReadConsistencyLevel() {
			return ConsistencyLevel.ALL;
		}

		@Override
		ConsistencyLevel getWriteConsistencyLevel() {
			return ConsistencyLevel.ALL;
		}
	}

	static class WeakHandle<@Weak V> extends CassandraHandle<V> {

		WeakHandle(CassandraDatabase database, CassandraDatabase.ObjectTable<V> table, UUID key, Class<V> clazz) {
			super(database, table, key, clazz);
		}

		@Override
		ConsistencyLevel getReadConsistencyLevel() {
			return ConsistencyLevel.ONE;
		}

		@Override
		ConsistencyLevel getWriteConsistencyLevel() {
			return ConsistencyLevel.ONE;
		}
	}
}
