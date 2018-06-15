package de.tudarmstadt.consistency.demo.legacy.example;

import com.datastax.driver.core.utils.UUIDs;
import de.tudarmstadt.consistency.demo.legacy.ConsistencyObject;
import de.tudarmstadt.consistency.demo.legacy.HighValue;
import de.tudarmstadt.consistency.demo.legacy.LowValue;
import de.tudarmstadt.consistency.checker.qual.Strong;

import java.util.UUID;

public class Customer extends ConsistencyObject {

    public HighValue<@Strong String> name;
    public HighValue<@Strong Integer> amount;
    public LowValue<Integer> loyaltyPoints;
    public UUID id;

    private CustomerConnector connector;

    public static UUID getNewID(){
        return UUIDs.random();
    }

    public Customer(Customer c){
        this(c.id, c.getName(), c.getBalance(), c.getLoyaltyPoints(), c.connector);
    }

    public Customer(UUID uuid, CustomerConnector connector) {
        this(uuid, null, null, null, connector);
    }

    public Customer(@Strong String n, CustomerConnector connector) {
        this(Customer.getNewID(), n, null, null, connector);
    }

    @SuppressWarnings("consistency")
    public Customer(UUID uuid, @Strong String n, @Strong Integer amount, Integer loyaltyPoints, CustomerConnector connector) {
        this.id = uuid;
        this.connector = connector;
        connector.useKeyspace("exampleApplication");
        this.name = new HighValue<>(n,
                connector.getSession(),
                () -> connector.getName(this),
                (@Strong String value) -> connector.setName(this, value),
                this);
        this.amount = new HighValue<>(amount,
                connector.getSession(),
                () -> connector.getBalance(this),
                (@Strong Integer value) -> connector.setBalance(this, value),
                this);
        this.loyaltyPoints = new LowValue<>(loyaltyPoints,
                connector.getSession(),
                () -> connector.getLoyaltyPoints(this),
                value -> connector.setLoyaltyPoints(this, value),
                this);
        this.name.sync();
        this.amount.sync();
        this.loyaltyPoints.sync();
    }

    @Strong
    public int getBalance() {
        return amount.value();
    }

    public void setBalance(@Strong int balance) {
        amount.setValue(balance);
    }

    public void withdraw(@Strong int s) {
        amount.perform(value -> {
            amount.setValue(value - s);
            return null;
        }
        );
    }

    @Strong
    public String getName() {
        return name.value();
    }

    public void setName(@Strong String n) {
        name.setValue(n);
    }

    public int getLoyaltyPoints() {
        return loyaltyPoints.value();
    }

    public void setLoyaltyPoints(int loyalty) {
        loyaltyPoints.setValue(loyalty);
    }
}
