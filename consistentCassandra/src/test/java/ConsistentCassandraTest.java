import org.junit.After;
import org.junit.Before;
import org.junit.Test;

public class ConsistentCassandraTest {

    private Integer port = 9042;
    private String node = "localhost";
    private Bank bank;

    @Before
    public void setUp() {

        BankConnector connector = new BankConnector();
        connector.connect(node, port);
        bank = new Bank(connector);
    }

    @Test
    public void simpleTest() {
        bank.addCustomer(new Customer("Peter", 2000));
    }

    @After
    public void tearDown(){
        bank.close();
    }
}
