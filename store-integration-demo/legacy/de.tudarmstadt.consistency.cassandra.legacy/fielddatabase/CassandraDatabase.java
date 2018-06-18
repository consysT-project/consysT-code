package de.tudarmstadt.consistency.demo.legacy.fielddatabase;

import com.datastax.driver.core.*;
import com.datastax.driver.core.querybuilder.QueryBuilder;
import com.google.common.collect.Maps;
import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.demo.legacy.blobdatabase.CassandraTable;
import de.tudarmstadt.consistency.store.Handle;
import de.tudarmstadt.consistency.store.Store;
import de.tudarmstadt.consistency.store.utils.Log;

import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.nio.ByteBuffer;
import java.util.*;

import static com.datastax.driver.core.querybuilder.QueryBuilder.eq;


/**
 * Created on 18.05.18.
 *
 * @author Mirko Köhler
 */

public class CassandraDatabase implements Store<UUID>, AutoCloseable {

	private final static String DEFAULT_KEYSPACE = "keyspace_consistency";

	private static final Integer DEFAULT_PORT = 9042;

	private static final String LOCAL_NODE = "localhost";
	private static final String TEST_CLUSTER_NODE = "127.0.0.1";


	private static final String DEFAULT_TABLE_NAME = "table_objects";


	private TupleType FOREIGN_KEY_DATA_TYPE = null;

	private final String hostname;
	private final int port;
	private final String keyspaceName;

	private Cluster cluster;
	private Session session;

	//Map from table names to tables. The table name depends on the class of objects stored in the table.
	//TODO: Convert to Map of ~Class->Table? Problem: How to get the class from Cassandra foreign keys.
	private final Map<String, ObjectTable> data = Maps.newHashMap();


	private CassandraDatabase(String hostname, int port) {
		this.hostname = hostname;
		this.port = port;
		this.keyspaceName = DEFAULT_KEYSPACE;
	}

	public static CassandraDatabase create(String hostname, int port) {
		CassandraDatabase database = new CassandraDatabase(hostname, port);
		database.initialize();

		return database;
	}

	public static CassandraDatabase local() {
		return create(TEST_CLUSTER_NODE, DEFAULT_PORT);
	}

	@Override
	@SuppressWarnings("consistency")
	public <T> Handle<T> obtain(UUID id, Class<T> valueClass, Class<?> consistencyLevel) {

		ObjectTable<T> table = getTableFor(valueClass);

		if (Objects.equals(consistencyLevel, Weak.class)) {
			return new CassandraHandle.WeakHandle<T>(this, table, id, valueClass);
		} else if (Objects.equals(consistencyLevel, Strong.class)) {
			return new CassandraHandle.StrongHandle<T>(this, table, id, valueClass);
		}

		throw new IllegalArgumentException("unknown consistency level");
	}

	private <V> ObjectTable<V> getTableFor(Class<V> clazz) {
		String name = getTableName(clazz);
		return data.computeIfAbsent(name, c -> createTable(clazz));
	}


	private void initialize() {
		connect(hostname, port, 3);
	}

	@Override
	public void close() {
		session.close();
		cluster.close();
	}

	/**
	 *
	 * @param address
	 * @param portNumber The port number where Cassandra can be contacted. Default is 9042.
	 * @param replicationFactor
	 */
	private synchronized void connect(String address, int portNumber, int replicationFactor) {

		cluster = Cluster.builder().addContactPoint(address).withPort(portNumber).build();

		//The datatype for foreign keys has to be defined in the cluster.
		FOREIGN_KEY_DATA_TYPE = cluster.getMetadata().newTupleType(DataType.text(), DataType.uuid());

		session = cluster.newSession();

		//Strategy NetworkTopologyStrategy does not support a replication factor.
		String replicationStrategy = "SimpleStrategy";

		execute("DROP KEYSPACE IF EXISTS " + keyspaceName);
		execute("CREATE KEYSPACE " +
			keyspaceName + " WITH replication = {" +
			"'class':'" + replicationStrategy + "'," +
			"'replication_factor':" + replicationFactor +
			"};"
		);

		session = cluster.connect(keyspaceName);
	}

	private ResultSet execute(String query) {
		Log.info(CassandraDatabase.class, "executing query:\t" + query);
		return session.execute(query);
	}


	private <V> ObjectTable<V> createTable(Class<V> clazz) {
		ObjectTable<V> table = new ObjectTable<>(keyspaceName, clazz);
		table.initialize();
		return table;
	}

	private static String getTableName(Class<?> clazz) {
		return "table_" + clazz.getSimpleName();
	}

	class ObjectTable<T> implements CassandraTable {

		private final static String ID_COLUMN_NAME = "id_";

		private final String keyspaceName;
		private final Class<T> clazz;

//		private final String[] columnNames;

		ObjectTable(String keyspaceName, Class<T> clazz) {
			this.keyspaceName = keyspaceName;
			this.clazz = clazz;

//			//Initialize column names
//			Field[] fields = clazz.getFields();
//			columnNames = new String[fields.length + 1];
//
//			columnNames[0] = ID_COLUMN_NAME;
//			int i = 1;
//			for (Field f : fields) {
//				columnNames[i] = getColumnName(f);
//			}

		}

		@Override
		public void initialize() {
			execute("drop table if exists " + getTableName() );

			StringBuilder query = new StringBuilder();

			query.append("create table ").append(getTableName()). append(" (").append(ID_COLUMN_NAME).append(" uuid primary key");


			for (Field field : clazz.getFields()) {
				query.append(", ").append(getColumnDecl(field));
			}

			query.append(");");

			execute(query.toString());
		}

		private String getColumnName(Field field) {
			String name = field.getName();

			if (Objects.equals(name, ID_COLUMN_NAME)) {
				throw new IllegalArgumentException("cannot create table for objects containing field " + ID_COLUMN_NAME);
			}

			return field.getName();
		}

		private String[] getColumnNames() {
			Field[] fields = clazz.getFields();
			String[] columnNames = new String[fields.length + 1];

			columnNames[0] = ID_COLUMN_NAME;
			int i = 1;
			for (Field f : fields) {
				columnNames[i] = getColumnName(f);
				i++;
			}

			return columnNames;
		}

		private String getColumnDecl(Field field) {
			Class<?> fType = field.getType();

			final DataType typeDecl;

			if (int.class.equals(fType)) {
				typeDecl = DataType.varint();
			} else if (String.class.equals(fType)) {
				typeDecl =  DataType.varchar();
			} else if (Handle.class.isAssignableFrom(fType)) {
				typeDecl = FOREIGN_KEY_DATA_TYPE;
			} else {
				typeDecl = DataType.blob();
			}

			//TODO: Use column definition(?) instead of string
			return  getColumnName(field) + " " + typeDecl;
		}

		public void insertInto(UUID id, T value, ConsistencyLevel level) {
			String query = QueryBuilder
					.insertInto(getTableName())
					.values(getColumnNames(), objectToCassandra(id, value))
					.setConsistencyLevel(level)
					.toString();

			execute(query);
		}

		public T select(UUID id, ConsistencyLevel level) {
			ResultSet result = execute(
					QueryBuilder.select().from(getTableName())
							.where(eq(ID_COLUMN_NAME, id))
							.setConsistencyLevel(level)
							.toString()
			);

			List<Row> rows = result.all();

			if (rows.isEmpty()) {
				return null;
			} else if (rows.size() == 1) {
				return cassandraToObject(rows.get(0));
			} else {
				throw new IllegalStateException("can not retrieve more than 1 row, but got:\n" + rows);
			}
		}

		private T cassandraToObject(Row row) {
			//row[0] == id. Not needed for creating the object.

			Constructor[] constructors = clazz.getDeclaredConstructors();
			if (constructors.length != 1) {
				throw new IllegalArgumentException("only record classes with 1 constructor are supported");
			}

			try {
				Constructor constructor = constructors[0];

				Object[] arguments = new Object[constructor.getParameterCount()];

				int i = 0;
				for (ColumnDefinitions.Definition def : row.getColumnDefinitions()) {
					if (i == 0) {
						i++;
						continue;
					}

					Class<?> cast;


					DataType type = def.getType();

					if (type.equals(DataType.varchar())) {
						cast = String.class;
					} else if (type.equals(DataType.varint())) {
						cast = int.class;
					} else if (type.equals(DataType.uuid())) {
						//TODO: initialize correct handle.
						cast = Object.class;
					} else if (type.equals(DataType.blob())){
						cast = ByteBuffer.class;
					} else {
						cast = null;
					}

					arguments[i - 1] = row.get(i, cast);

					i++;
				}

				Log.info(getClass(), Arrays.toString(arguments));
				Log.info(getClass(), row);

				return (T) constructor.newInstance(arguments);
			} catch (InstantiationException e) {
				e.printStackTrace();
			} catch (IllegalAccessException e) {
				e.printStackTrace();
			} catch (InvocationTargetException e) {
				e.printStackTrace();
			}

			return null;
		}

		private Object[] objectToCassandra(UUID id, T value) {

			Field[] fields = clazz.getFields();
			Object[] columns = new Object[fields.length + 1];

			columns[0] = id;
			int i = 1;
			for (Field f : fields) {
				columns[i] = getColumnValue(f, value);
				i++;
			}

			return columns;
		}

		private Object getColumnValue(Field field, T value) {
			Class<?> fType = field.getType();

			try {

				if (int.class.equals(fType)) {
					return field.get(value);
				} else if (String.class.equals(fType)) {
					return field.get(value);
				} else if (Handle.class.isAssignableFrom(fType)) {
					Object fieldValue = field.get(value);
					if (fieldValue instanceof CassandraHandle) {
						CassandraHandle fieldHandle = (CassandraHandle) fieldValue;
						return FOREIGN_KEY_DATA_TYPE.newValue(CassandraDatabase.getTableName(fieldHandle.getValueType()), fieldHandle.getKey());
					} else {
						throw new IllegalArgumentException("can only use cassandra handles");
					}

				} else {
					throw new UnsupportedOperationException("blobs currently unsupported");
				}

			} catch (IllegalAccessException e) {
				e.printStackTrace();
				return null;
			}
		}

		@Override
		public String getTableName() {
			return CassandraDatabase.getTableName(clazz);
		}




	}

}
