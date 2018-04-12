public class Customer {

    static int id_count = 0;

    public HighValue<String> name;
    public HighValue<Integer> amount;
    public int id;

    private CustomerConnector connector;

    public static int getNewID(){
        id_count++;
        return id_count;
    }

    public Customer(String n, CustomerConnector connector){
        this.id = Customer.getNewID();
        this.connector = connector;
        this.name = new HighValue<>(n, connector,
                () -> {
                    return connector.getName(this);
                },
                value -> {
                    connector.setName(this, value);
                });
        this.amount = new HighValue<>(0, connector,
                () -> {
                    return connector.getBalance(this);
                },
                value -> {
                    connector.setBalance(this, value);
                });
    }

    public int getBalance() {
        return connector.getBalance(this);
    }

    public void setBalance(int balance) {
        connector.setBalance(this, balance);
    }

    public void withdraw(int amount) {
        connector.withdraw(this, amount);
    }

    public String getName() {
        return connector.getName(this);
    }

    public void setName(String name) {
        connector.setName(this, name);
    }
}
