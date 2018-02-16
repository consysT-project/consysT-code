import com.datastax.driver.core.*;
import com.github.allprojects.consistencyTypes.qual.High;
import com.github.allprojects.consistencyTypes.qual.Low;

public class ConsistentCassandraConnector {

    private Cluster cluster;
    private Session session;

    public void connect(String node, Integer port) {
        Cluster.Builder b = Cluster.builder().addContactPoint(node);
        if (port != null) {
            b.withPort(port);
        }
        cluster = b.build();
        session = cluster.connect();
    }


    @High public ResultSet executeAll(@High Statement statement){
        statement.setConsistencyLevel(ConsistencyLevel.ALL);
        @SuppressWarnings("consistency")
        @High ResultSet result = session.execute(statement);
        return result;
    }

    @Low public ResultSet executeSingle(@Low Statement statement){
        statement.setConsistencyLevel(ConsistencyLevel.ONE);
        return session.execute(statement);
    }

    public Session getSession() {
        return this.session;
    }

    public void close() {
        session.close();
        cluster.close();
    }
}
