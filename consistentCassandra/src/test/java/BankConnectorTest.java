import com.github.allprojects.consistencyTypes.qual.High;
import com.github.allprojects.consistencyTypes.qual.Low;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;

public class BankConnectorTest {

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
        @High Customer c = new Customer("Peter");
        bank.addCustomer(c);
        assert bank.getBalance(c) == 0;
    }

    @Low public int someInconsistentCalculation() { return 42; }

    @Test
    public void withdrawalTest() {
        @High int amountA = 1000;
        @Low int amountB = someInconsistentCalculation();
        int amountC = someInconsistentCalculation();

        @High Customer c = new Customer("Peter");
        bank.addCustomer(c);
        bank.withdraw(c, amountA);
        assert bank.getBalance(c) == -1000;
        bank.withdraw(c, -amountA);
        assert bank.getBalance(c) == 0;
        // :: error: (argument.type.incompatible)
        bank.withdraw(c, amountB);
        // :: error: (argument.type.incompatible)
        bank.withdraw(c, amountC);
    }

    @After
    public void tearDown(){
        bank.close();
    }
}
