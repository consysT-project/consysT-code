import com.github.allprojects.consistencyTypes.qual.High;

public class Bank {

    private BankConnector connector;

    public Bank(BankConnector conn){
        this.connector = conn;
        connector.createKeyspace("bank", "SimpleStrategy", 1);
        connector.createCustomerTable();
    }

    public void addCustomer(Customer c){
        connector.addCustomer(c);
    }

    public void close(){
        connector.dropKeyspace("bank");
    }
}
