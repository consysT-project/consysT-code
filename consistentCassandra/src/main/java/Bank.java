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

    public int getBalance(Customer c) { return connector.getBalance(c); }

    public void withdraw(Customer c, int amount) { connector.withdraw(c, amount); }

    public void close(){
        connector.dropKeyspace("bank");
    }
}
