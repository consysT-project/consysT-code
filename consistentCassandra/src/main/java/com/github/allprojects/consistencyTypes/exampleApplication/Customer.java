package com.github.allprojects.consistencyTypes.exampleApplication;

import com.github.allprojects.consistencyTypes.cassandraInterface.HighValue;
import com.github.allprojects.consistencyTypes.cassandraInterface.LowValue;
import com.github.allprojects.consistencyTypes.cassandraInterface.Wrappable;
import com.github.allprojects.consistencyTypes.qual.High;
import org.apache.cassandra.utils.UUIDGen;

import java.util.UUID;

public class Customer extends Wrappable {

    public HighValue<@High String> name;
    public HighValue<@High Integer> amount;
    public LowValue<Integer> loyaltyPoints;
    public UUID id;

    private CustomerConnector connector;

    public static UUID getNewID(){
        return UUIDGen.getTimeUUID();
    }

    public Customer(Customer c){
        this(c.id, c.getName(), c.getBalance(), c.getLoyaltyPoints(), c.connector);
    }

    public Customer(UUID uuid, CustomerConnector connector) {
        this(uuid, null, null, null, connector);
    }

    public Customer(@High String n, CustomerConnector connector) {
        this(Customer.getNewID(), n, null, null, connector);
    }

    public Customer(UUID uuid, @High String n, @High Integer amount, Integer loyaltyPoints, CustomerConnector connector) {
        this.id = uuid;
        this.connector = connector;
        connector.useKeyspace("com/github/allprojects/consistencyTypes/exampleApplication");
        this.name = new HighValue<>(n,
                connector.getSession(),
                () -> connector.getName(this),
                value -> connector.setName(this, value),
                this);
        this.amount = new HighValue<>(amount,
                connector.getSession(),
                () -> connector.getBalance(this),
                value -> connector.setBalance(this, value),
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

    @High
    public int getBalance() {
        return amount.value();
    }

    public void setBalance(@High int balance) {
        amount.setValue(balance);
    }

    public void withdraw(@High int s) {
        amount.perform(value -> {
            amount.setValue(value - s);
            return null;
        }
        );
    }

    @High
    public String getName() {
        return name.value();
    }

    public void setName(@High String n) {
        name.setValue(n);
    }

    public int getLoyaltyPoints() {
        return loyaltyPoints.value();
    }

    public void setLoyaltyPoints(int loyalty) {
        loyaltyPoints.setValue(loyalty);
    }
}
