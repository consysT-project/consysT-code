package de.tu_darmstadt.consistency_types.cassandra;

import com.datastax.driver.core.Cluster;
import com.datastax.driver.core.Session;
import com.datastax.driver.core.querybuilder.QueryBuilder;
import de.tu_darmstadt.consistency_types.checker.qual.Local;

public class ConsistentCassandraConnector {
    private @Local Cluster cluster;
    private @Local Session session;

    public Cluster getCluster() {
        return this.cluster;
    }

    public @Local Session getSession() {
        return this.session;
    }

    @SuppressWarnings("consistency")
    public void connect(String node, Integer port) {
        Cluster.@Local Builder b = Cluster.builder().addContactPoint(node);

        if (port != null) {
            b.withPort(port);
        }


        cluster = b.build();
        session = cluster.connect();
    }

    public void close() {
        session.close();
        cluster.close();
    }

    public void createKeyspace(String keyspaceName, String replicationStrategy, int replicationFactor) {


        String query = "CREATE KEYSPACE IF NOT EXISTS " +
                keyspaceName + " WITH replication = {" +
                "'class':'" + replicationStrategy +
                "','replication_factor':" + replicationFactor +
                "};";
        session.execute(query);
        this.useKeyspace(keyspaceName);
    }

	@SuppressWarnings("consistency")
    public void useKeyspace(String keyspaceName){
        session = cluster.connect(keyspaceName);
    }

	@SuppressWarnings("consistency")
    public void dropKeyspace(String name){
        @Local String query = "DROP KEYSPACE " + name;
        session.execute(query);
    }
}
