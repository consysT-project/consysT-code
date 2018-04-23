package bank;

import cassandra.HighValue;
import cassandra.LowValue;
import cassandra.Wrappable;
import org.apache.cassandra.utils.UUIDGen;

import java.util.UUID;

public class Customer extends Wrappable {

    public HighValue<String> name;
    public HighValue<Integer> amount;
    public LowValue<Integer> loyaltyPoints;
    public UUID id;

    private CustomerConnector connector;

    public static UUID getNewID(){
        return UUIDGen.getTimeUUID();
    }


    public Customer(Customer c){
        this(c.id, c.getName(), c.getBalance(), c.connector);
    }

    public Customer(String n, CustomerConnector connector){
        this.id = Customer.getNewID();
        this.connector = connector;
        connector.useKeyspace("bank");
        this.name = new HighValue<>(n,
                connector.getSession(),
                () -> connector.getName(this),
                value -> connector.setName(this, value),
                this);
        this.amount = new HighValue<>(0,
                connector.getSession(),
                () -> connector.getBalance(this),
                value -> connector.setBalance(this, value),
                this);
        this.loyaltyPoints = new LowValue<>(0,
                connector.getSession(),
                () -> connector.getLoyaltyPoints(this),
                value -> connector.setLoyaltyPoints(this, value),
                this);
    }

    public Customer(UUID uuid, String n, int amount, CustomerConnector connector){
        this(n, connector);
        this.id = uuid;
        this.setBalance(amount);
    }

    public int getBalance() {
        return amount.value();
    }

    public void setBalance(int balance) {
        amount.setValue(balance);
    }

    public void withdraw(int s) {
        amount.perform(value -> {
            amount.setValue(value - s);
            return null;
        }
        );
    }

    public String getName() {
        return name.value();
    }

    public void setName(String n) {
        name.setValue(n);
    }

    public int getLoyaltyPoints() {
        return loyaltyPoints.value();
    }

    public void setLoyaltyPoints(int loyalty) {
        loyaltyPoints.setValue(loyalty);
    }
}
