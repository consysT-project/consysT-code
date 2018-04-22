import bank.Bank;
import bank.BankConnector;
import bank.Customer;
import bank.CustomerConnector;
import com.github.allprojects.consistencyTypes.qual.High;
import com.github.allprojects.consistencyTypes.qual.Low;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

public class BankConnectorTest {

    private Integer port = 9042;
    private String node = "localhost";
    private Bank bank;
    private CustomerConnector customerConnector;

    @Before
    public void setUp() {
        BankConnector connector = new BankConnector();
        customerConnector = new CustomerConnector();
        connector.connect(node, port);
        customerConnector.connect(node, port);
        bank = new Bank(connector);
    }

    @Test
    public void simpleTest() {
        Customer c = new Customer("Peter", customerConnector);
        bank.addCustomer(c);
        assert c.getBalance() == 0;
    }

    @Test
    public void withdrawalTest() {
        Customer c = new Customer("Peter", customerConnector);
        bank.addCustomer(c);
        c.withdraw(1000);
        assert c.getBalance() == -1000;
    }

    @After
    public void tearDown(){
        bank.close();
    }
}
