package de.tu_darmstadt.consistency_types.example2;

import com.datastax.driver.core.Cluster;
import com.datastax.driver.core.Session;
import de.tu_darmstadt.consistency_types.checker.qual.Strong;
import de.tu_darmstadt.consistency_types.checker.qual.Weak;
import de.tu_darmstadt.consistency_types.value.Database;
import de.tu_darmstadt.consistency_types.value.StrongValue;
import de.tu_darmstadt.consistency_types.value.WeakValue;

import java.io.Serializable;
import java.util.UUID;


/**
 * Created on 18.05.18.
 *
 * @author Mirko Köhler
 */

public class CassandraDatabase implements Database<UUID> {

	private final static String DEFAULT_KEYSPACE = "keyspace_consistency";

	private static final Integer DEFAULT_PORT = 9042;

	private static final String LOCAL_NODE = "localhost";
	private static final String TEST_CLUSTER_NODE = "127.0.0.1";


	private static final String DEFAULT_TABLE_NAME = "table_data";


	private final String hostname;
	private final int port;

	private Cluster cluster;
	private Session session;

	private CassandraTable data;

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


	class StrongConnector implements DatabaseConnector<UUID> {
		public <V extends @Strong Serializable> StrongValue<V> obtainValue(UUID key) {
			return new CassandraValue.StrongValue<V>(session, data, key);
		}
	}

	class WeakConnector implements DatabaseConnector<UUID> {
		public <V extends @Weak Serializable> WeakValue<V> obtainValue(UUID key) {
			return new CassandraValue.WeakValue<V>(session, data, key);
		}
	}

	@SuppressWarnings("unchecked")
	private final DatabaseConnector<UUID>[] connectors = new DatabaseConnector[] {
			new StrongConnector(),
			new WeakConnector()
	};

	@Override
	public DatabaseConnector<UUID>[] connectors() {
		return connectors;
	}

	public StrongConnector strong() {
		return (StrongConnector) connectors[0];
	}
	public WeakConnector weak() {
		return (WeakConnector) connectors[1];
	}


	@Override
	public void initialize() {
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
		this.data = new CassandraTable(keyspaceName, DEFAULT_TABLE_NAME);
		this.data.create();


	}


	class CassandraTable {

		private final String keyspaceName;
		private final String tableName;

		CassandraTable(String keyspaceName, String tableName) {
			this.keyspaceName = keyspaceName;
			this.tableName = tableName;
		}

		void create() {
			session.execute("DROP TABLE IF EXISTS " + tableName );
			session.execute("CREATE TABLE " + tableName + " (" +
					getKeyName() + " uuid PRIMARY KEY, " +
					getDataName() + " blob);");
		}

		String getTableName() {
			return tableName;
		}

		String getKeyName() {
			return "id";
		}

		String getDataName() {
			return "data";
		}

	}

}
