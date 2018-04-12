import com.github.allprojects.consistencyTypes.qual.High;

public class Bank {

    private BankConnector connector;

    public Bank(BankConnector conn){
        this.connector = conn;
        connector.createKeyspace("bank", "SimpleStrategy", 1);
        connector.createCustomerTable();
    }

    public void addCustomer(@High Customer c){
        connector.addCustomer(c);
    }

    public int getBalance(Customer c) { return connector.getBalance(c); }

    public void withdraw(@High Customer c, @High int amount) { connector.withdraw(c, amount); }

    public void close(){
        connector.dropKeyspace("bank");
    }
}
