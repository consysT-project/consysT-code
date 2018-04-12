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
        bank = new Bank(connector);
    }

    @Test
    public void simpleTest() {
        Customer c = new Customer("Peter", customerConnector);
        bank.addCustomer(c);
        assert c.getBalance() == 0;
    }

    @Low public int someInconsistentCalculation() { return 42; }

    @Test
    public void withdrawalTest() {
        @High int amountA = 1000;
        @Low int amountB = someInconsistentCalculation();
        int amountC = someInconsistentCalculation();

        Customer c = new Customer("Peter", customerConnector);
        bank.addCustomer(c);
        c.withdraw(amountA);
        assert c.getBalance() == -1000;
        c.withdraw(-amountA);
        assert c.getBalance() == 0;
        // :: error: (argument.type.incompatible)
        c.withdraw(amountB);
        // :: error: (argument.type.incompatible)
        c.withdraw(amountC);
    }

    @After
    public void tearDown(){
        bank.close();
    }
}
