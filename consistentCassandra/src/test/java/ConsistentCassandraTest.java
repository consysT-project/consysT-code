import com.github.allprojects.consistencyTypes.qual.Low;
import org.junit.Before;
import org.junit.Test;

public class ConsistentCassandraTest {

    private ConsistentCassandraConnector client;
    private KeyspaceRepository schemaRepository;

    @Before
    public void connect() {
        client = new ConsistentCassandraConnector();
        client.connect("127.0.0.1", 9142);
        schemaRepository = new KeyspaceRepository(client.getSession());
    }

    @Test
    public void simpleTest() {
        String keyspaceName = "library";
        schemaRepository.createKeyspace(keyspaceName, "SimpleStrategy", 1);
    }
}
