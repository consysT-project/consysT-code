package de.tudarmstadt.consistency.demo.legacy.fielddatabase;

import de.tudarmstadt.consistency.store.Handle;

import java.lang.reflect.Field;
import java.util.UUID;

/**
 * Created on 12.06.18.
 *
 * @author Mirko Köhler
 */
public class CassandraColumns<T> {

	private final CassandraTable<T> table;

	private final CassandraColumn[] columns;


	public CassandraColumns(CassandraTable<T> table, CassandraColumn idColumn) {
		this.table = table;

		Field[] fields = table.getElementClass().getFields();
		columns = new CassandraColumn[fields.length + 1];

		columns[0] = idColumn;

		int i = 1;
		for (Field f : fields) {
			columns[i] = CassandraColumn.from(f);
			i++;
		}
	}

	public CassandraColumn getIdColumn() {
		return columns[0];
	}

	public Object[] asColumns(UUID id, T object) {

		Class<T> elementClass = table.getElementClass();
		Class<?> objectClass = object.getClass();

		if (!objectClass.equals(elementClass)) {
			throw new IllegalArgumentException("object class is not the class of the columns. expected <" + table.getElementClass() + "> but got <" + object.getClass() + ">");
		}

		Field[] fields = objectClass.getFields();
		Object[] result = new Object[fields.length + 1];

		result[0] = id;

		try {

			int i = 1;
			for (Field f : fields) {
				Object fieldValue = f.get(object);
				result[i] = convertToCassandraValue(fieldValue, f, columns[i]);
				i++;
			}
			return result;

		} catch (IllegalAccessException e) {
			e.printStackTrace();
			throw new IllegalArgumentException("field not accessible.", e);
		}

	}

	private Object convertToCassandraValue(Object fieldValue, Field field, CassandraColumn column) {

		Class<?> fieldClass = field.getDeclaringClass();

		if (fieldValue instanceof Integer) {
			return fieldValue;
		} else if (fieldValue instanceof String) {
			return fieldValue;
		} else if (fieldValue instanceof Handle) {
			//TODO: Add reference

//			Object fieldValue = field.get(value);
//			if (fieldValue instanceof CassandraHandle) {
//				CassandraHandle fieldHandle = (CassandraHandle) fieldValue;
//				return FOREIGN_KEY_DATA_TYPE.newValue(CassandraDatabase.getTableName(fieldHandle.getValueType()), fieldHandle.getKey());
//			} else {
//				throw new IllegalArgumentException("can only use cassandra handles");
//			}

			return fieldValue;


		} else {
			throw new UnsupportedOperationException("blobs currently unsupported");
		}

	}


}
