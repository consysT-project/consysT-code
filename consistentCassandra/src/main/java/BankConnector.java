import com.datastax.driver.core.*;
import com.datastax.driver.core.querybuilder.QueryBuilder;
import com.github.allprojects.consistencyTypes.qual.High;
import com.github.allprojects.consistencyTypes.qual.Low;

public class BankConnector {
    private Cluster cluster;
    private Session session;

    private final String customerTableName = "customers";
    private final String idKey = "id";
    private final String nameKey = "name";
    private final String amountKey = "amount";

    public BankConnector(){

    }

    public void connect(String node, Integer port) {
        Cluster.Builder b = Cluster.builder().addContactPoint(node);
        if (port != null) {
            b.withPort(port);
        }
        cluster = b.build();
        session = cluster.connect();
    }


    @High
    public ResultSet executeAll(@High Statement statement){
        statement.setConsistencyLevel(ConsistencyLevel.ALL);
        @SuppressWarnings("consistency")
        @High ResultSet result = session.execute(statement);
        return result;
    }

    @Low
    public ResultSet executeSingle(@Low Statement statement){
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

    public void createCustomerTable(){
        session.execute("CREATE TABLE " + customerTableName + " ("+ idKey +" int primary key, "+ nameKey + " varchar, "+ amountKey +" int);");
    }

    public void addCustomer(Customer c){
        String query = QueryBuilder.insertInto(customerTableName).values(new String[]{idKey, nameKey, amountKey}, new Object[]{c.id, c.name, c.amount}).getQueryString();
        SimpleStatement statement = new SimpleStatement(query);
        this.executeAll(statement);
    }
}
