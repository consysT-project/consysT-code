package de.tudarmstadt.consistency.cassandra.legacy.fielddatabase;

import com.datastax.driver.core.DataType;

/**
 * Created on 12.06.18.
 *
 * @author Mirko Köhler
 */
public class CassandraTable<T> {

	private final Class<T> elementClass;
	private final CassandraColumns<T> columns;


	public CassandraTable(String idColumnName, Class<T> elementClass) {
		this.elementClass = elementClass;
		this.columns = new CassandraColumns<>(this, new CassandraColumn("__id", DataType.uuid()));
	}

	public Class<T> getElementClass() {
		return elementClass;
	}
}
