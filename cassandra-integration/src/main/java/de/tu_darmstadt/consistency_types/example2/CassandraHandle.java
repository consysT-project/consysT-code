package de.tu_darmstadt.consistency_types.example2;

import com.datastax.driver.core.ConsistencyLevel;
import com.datastax.driver.core.ResultSet;
import com.datastax.driver.core.Row;
import com.datastax.driver.core.Session;
import de.tu_darmstadt.consistency_types.checker.qual.Strong;
import de.tu_darmstadt.consistency_types.checker.qual.Weak;
import de.tu_darmstadt.consistency_types.store.utils.Log;
import de.tu_darmstadt.consistency_types.store.impl.SerializerHandle;

import java.io.IOException;
import java.nio.ByteBuffer;
import java.util.List;
import java.util.UUID;

import static com.datastax.driver.core.querybuilder.QueryBuilder.*;

/**
 * Created on 18.05.18.
 *
 * @author Mirko Köhler
 */
abstract class CassandraHandle<V> extends SerializerHandle<V> {

	private final Session session;
	private final UUID key;
	private final CassandraDatabase.BlobTable table;

	CassandraHandle(Session session, CassandraDatabase.BlobTable table, UUID key) {
		this.session = session;
		this.key = key;
		this.table = table;
	}

	abstract ConsistencyLevel getReadConsistencyLevel();
	abstract ConsistencyLevel getWriteConsistencyLevel();

	@Override
	protected byte[] readBytes() {
		ResultSet result = session.execute(
				select().from(table.getTableName())
						.where(eq(table.getKeyName(), key))
						.setConsistencyLevel(getReadConsistencyLevel())
		);

		List<Row> rows = result.all();

		if (rows.isEmpty()) {
			return null;
		} else if (rows.size() == 1) {
			ByteBuffer data = rows.get(0).get(table.getDataName(), ByteBuffer.class);
			return data.array();
		} else {
			throw new IllegalStateException("can not retrieve more than 1 row, but got:\n" + rows);
		}
	}

	@Override
	public V get() throws IOException, ClassNotFoundException {
		V result = super.get();
		Log.info(CassandraHandle.class, "Reading <" + result + "> with " + getReadConsistencyLevel());
		return result;
	}



	@Override
	protected void writeBytes(byte[] bytes) {
		ByteBuffer data = ByteBuffer.wrap(bytes);

		//Store object in database
		session.execute(
				//Upsert operation: if the row already exists, then it is updated. Does not provide any concurrency control.
				insertInto(table.getTableName())
						.values(new String[] {table.getKeyName(), table.getDataName()}, new Object[] {key, data} )
						.setConsistencyLevel(getWriteConsistencyLevel())
		);
	}

	@Override
	public void set(V value) throws IOException {
		Log.info(CassandraHandle.class, "Writing <" + value + "> with " + getReadConsistencyLevel());
		super.set(value);
	}

	static class StrongHandle<@Strong V> extends CassandraHandle<V> {

		StrongHandle(Session session, CassandraDatabase.BlobTable table, UUID key) {
			super(session, table, key);
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

		WeakHandle(Session session, CassandraDatabase.BlobTable table, UUID key) {
			super(session, table, key);
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
