package cassandra;

import com.datastax.driver.core.*;
import com.github.allprojects.consistencyTypes.qual.High;
import com.github.allprojects.consistencyTypes.qual.Low;

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
        StringBuilder sb =
                new StringBuilder("CREATE KEYSPACE IF NOT EXISTS ")
                        .append(keyspaceName).append(" WITH replication = {")
                        .append("'class':'").append(replicationStrategy)
                        .append("','replication_factor':").append(replicationFactor)
                        .append("};");

        String query = sb.toString();
        session.execute(query);
        session = cluster.connect(keyspaceName);
    }

    public void dropKeyspace(String name){
        String query = "DROP KEYSPACE " + name;
        session.execute(query);
    }
}
