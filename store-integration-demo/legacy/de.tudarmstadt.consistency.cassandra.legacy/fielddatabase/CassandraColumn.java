package de.tudarmstadt.consistency.demo.legacy.fielddatabase;

import com.datastax.driver.core.DataType;
import de.tudarmstadt.consistency.store.Handle;

import java.lang.reflect.Field;

/**
 * Created on 12.06.18.
 *
 * @author Mirko Köhler
 */
public class CassandraColumn {
	private final String columnName;
	private final DataType dataType;

	public CassandraColumn(String columnName, DataType dataType) {
		this.columnName = columnName;
		this.dataType = dataType;
	}

	public static CassandraColumn from(Field field) {
		String columnName = field.getName();

		Class<?> fType = field.getType();


		if (int.class.equals(fType)) {
			return new CassandraColumn(columnName, DataType.varint());
		} else if (String.class.equals(fType)) {
			return new CassandraColumn(columnName, DataType.varchar());
		} else if (Handle.class.isAssignableFrom(fType)) {
//				Object fieldValue = field.read(value);
//				if (fieldValue instanceof CassandraHandle) {
//					CassandraHandle fieldHandle = (CassandraHandle) fieldValue;
//					return FOREIGN_KEY_DATA_TYPE.newValue(CassandraDatabase.getTableName(fieldHandle.getValueType()), fieldHandle.getKey());
//				} else {
//					throw new IllegalArgumentException("can only use cassandra handles");
//				}

			return null;

		} else {
			throw new UnsupportedOperationException("data type unsupported for creating objects: " + field);
		}


	}

	public String getColumnName() {
		return columnName;
	}

	public DataType getDataType() {
		return dataType;
	}
}
