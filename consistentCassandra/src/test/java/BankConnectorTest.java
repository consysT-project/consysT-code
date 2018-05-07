import com.github.allprojects.consistencyTypes.exampleApplication.Bank;
import com.github.allprojects.consistencyTypes.exampleApplication.BankConnector;
import com.github.allprojects.consistencyTypes.exampleApplication.Customer;
import com.github.allprojects.consistencyTypes.exampleApplication.CustomerConnector;
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
        bank.write();
        assert c.getBalance() == 0;
        printCustomerStatus(c);
    }

    @Test
    public void concurrentTest() {
        Customer klaus1 = new Customer("Klaus", customerConnector);
        bank.addCustomer(klaus1);
        bank.write();
        Customer klaus2 = new Customer(klaus1);
        klaus1.withdraw(1000);
        assert klaus2.getBalance() == klaus1.getBalance() && klaus1.getBalance() == -1000;
        klaus2.setBalance(1000000);
        assert klaus2.getBalance() == klaus1.getBalance() && klaus1.getBalance() == 1000000;
        assert klaus2.getLoyaltyPoints() == 0;
        klaus1.setLoyaltyPoints(5);
        assert klaus1.getLoyaltyPoints() == 5;
        assert klaus2.getLoyaltyPoints() == 0;
        assert klaus2.getLoyaltyPoints() == 0;
        assert klaus2.getLoyaltyPoints() == 0;
        assert klaus2.getLoyaltyPoints() == 5;
    }

    @Test
    public void collectionWrapperTest() {
        Customer peter = new Customer("Peter", customerConnector);
        Customer ulf = new Customer("Ulf", customerConnector);
        Customer otto = new Customer("Otto", customerConnector);
        bank.addCustomer(otto);
        bank.addCustomer(peter);
        bank.addCustomer(ulf);

        peter.setLoyaltyPoints(4867);
        otto.setLoyaltyPoints(35698);
        ulf.setLoyaltyPoints(34875);

        bank.write();
    }

    @Test
    public void withdrawalTest() {
        Customer c = new Customer("Peter", customerConnector);
        bank.addCustomer(c);
        bank.write();
        c.withdraw(1000);
        assert c.getBalance() == -1000;
        printCustomerStatus(c);
    }

    private void printCustomerStatus(Customer c){
        c.amount.perform((value) -> {
            if(value > 0){
                System.out.println(c.getName() + " hat " + value + " Euro Guthaben");
            } else if(value == 0){
                System.out.println(c.getName() + " hat kein Guthaben");
            } else {
                System.out.println(c.getName() + " hat " + value + " Euro Schulden");
            }
            return null;
        });
    }

    @After
    public void tearDown(){
        bank.close();
    }
}
