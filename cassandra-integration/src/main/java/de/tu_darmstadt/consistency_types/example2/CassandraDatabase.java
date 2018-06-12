package de.tu_darmstadt.consistency_types.example2;

import com.datastax.driver.core.Cluster;
import com.datastax.driver.core.Session;
import de.tu_darmstadt.consistency_types.checker.qual.Strong;
import de.tu_darmstadt.consistency_types.checker.qual.Weak;
import de.tu_darmstadt.consistency_types.store.Handle;
import de.tu_darmstadt.consistency_types.store.Store;

import java.util.Objects;
import java.util.UUID;


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


	private static final String DEFAULT_TABLE_NAME = "table_data";


	private final String hostname;
	private final int port;

	private Cluster cluster;
	private Session session;

	private BlobTable data;
	private BlobTable objectTable;

	private CassandraDatabase(String hostname, int port) {
		this.hostname = hostname;
		this.port = port;
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

		if (Objects.equals(consistencyLevel, Weak.class)) {
			return new CassandraHandle.WeakHandle<T>(session, data, id);
		} else if (Objects.equals(consistencyLevel, Strong.class)) {
			return new CassandraHandle.StrongHandle<T>(session, data, id);
		}

		throw new IllegalArgumentException("unknown consistency level");
	}


	private void initialize() {
		connect(hostname, port, DEFAULT_KEYSPACE, 3);
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
	 * @param keyspaceName
	 * @param replicationFactor
	 */
	private synchronized void connect(String address, int portNumber, String keyspaceName, int replicationFactor) {

		cluster = Cluster.builder().addContactPoint(address).withPort(portNumber).build();
		session = cluster.newSession();

		//Strategy NetworkTopologyStrategy does not support a replication factor.
		String replicationStrategy = "SimpleStrategy";

		session.execute("DROP KEYSPACE IF EXISTS " + keyspaceName);
		session.execute("CREATE KEYSPACE " +
			keyspaceName + " WITH replication = {" +
			"'class':'" + replicationStrategy + "'," +
			"'replication_factor':" + replicationFactor +
			"};"
		);

		session = cluster.connect(keyspaceName);


		//Initialize the data table
		this.data = new BlobTable(keyspaceName, DEFAULT_TABLE_NAME);
		this.data.initialize();


	}




	class BlobTable implements CassandraTable {

		private final String keyspaceName;
		private final String tableName;

		BlobTable(String keyspaceName, String tableName) {
			this.keyspaceName = keyspaceName;
			this.tableName = tableName;
		}

		@Override
		public void initialize() {
			session.execute("DROP TABLE IF EXISTS " + tableName );
			session.execute("CREATE TABLE " + tableName + " (" +
					getKeyName() + " uuid PRIMARY KEY, " +
					getDataName() + " blob);");
		}

		@Override
		public String getTableName() {
			return tableName;
		}

		public String getKeyName() {
			return "id";
		}

		public String getDataName() {
			return "data";
		}

	}

}
