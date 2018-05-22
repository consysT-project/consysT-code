package de.tu_darmstadt.consistency_types.example2;

import com.datastax.driver.core.ConsistencyLevel;
import com.datastax.driver.core.ResultSet;
import com.datastax.driver.core.Row;
import com.datastax.driver.core.Session;
import de.tu_darmstadt.consistency_types.checker.qual.Strong;
import de.tu_darmstadt.consistency_types.checker.qual.Weak;
import de.tu_darmstadt.consistency_types.utils.Log;
import de.tu_darmstadt.consistency_types.value.ByteArrayValue;
import de.tu_darmstadt.consistency_types.value.DatabaseValue;
import de.tu_darmstadt.consistency_types.value.StrongValue;

import java.io.IOException;
import java.io.Serializable;
import java.nio.ByteBuffer;
import java.util.List;
import java.util.UUID;

import static com.datastax.driver.core.querybuilder.QueryBuilder.*;

/**
 * Created on 18.05.18.
 *
 * @author Mirko Köhler
 */
abstract class CassandraValue<V extends Serializable> extends ByteArrayValue<V> implements DatabaseValue<V> {

	private final Session session;
	private final UUID key;
	private final CassandraDatabase.CassandraTable table;

	CassandraValue(Session session, CassandraDatabase.CassandraTable table, UUID key) {
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
	public V read() throws IOException, ClassNotFoundException {
		V result = super.read();
		Log.info(CassandraValue.class, "Reading <" + result + "> with " + getReadConsistencyLevel());
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
	public void write(V value) throws IOException {
		Log.info(CassandraValue.class, "Writing <" + value + "> with " + getReadConsistencyLevel());
		super.write(value);
	}

	static class StrongValue<V extends @Strong Serializable> extends CassandraValue<V> implements de.tu_darmstadt.consistency_types.value.StrongValue<V> {

		StrongValue(Session session, CassandraDatabase.CassandraTable table, UUID key) {
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

	static class WeakValue<V extends @Weak Serializable> extends CassandraValue<V> implements de.tu_darmstadt.consistency_types.value.WeakValue<V> {

		WeakValue(Session session, CassandraDatabase.CassandraTable table, UUID key) {
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
