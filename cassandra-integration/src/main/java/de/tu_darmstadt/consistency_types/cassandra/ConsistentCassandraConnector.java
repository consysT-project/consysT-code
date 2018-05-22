package de.tu_darmstadt.consistency_types.cassandra;

import com.datastax.driver.core.Cluster;
import com.datastax.driver.core.Session;
import com.datastax.driver.core.querybuilder.QueryBuilder;

public class ConsistentCassandraConnector {
    private Cluster cluster;
    private Session session;

    public Cluster getCluster() {
        return this.cluster;
    }

    public Session getSession() {
        return this.session;
    }

    public void connect(String node, Integer port) {
        Cluster.Builder b = Cluster.builder().addContactPoint(node);
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

    public void useKeyspace(String keyspaceName){
        session = cluster.connect(keyspaceName);
    }

    public void dropKeyspace(String name){
        String query = "DROP KEYSPACE " + name;
        session.execute(query);
    }
}
