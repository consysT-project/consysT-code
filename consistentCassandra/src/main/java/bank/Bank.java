package bank;

import cassandra.CollectionWrapper;
import cassandra.Wrappable;

import java.util.HashSet;

public class Bank extends Wrappable {

    private BankConnector connector;
    private CollectionWrapper<HashSet<Customer>, Customer> customer;

    public Bank(BankConnector conn){
        this.connector = conn;
        this.customer = new CollectionWrapper<>(new HashSet<>());
        connector.createKeyspace("bank", "SimpleStrategy", 1);
        connector.createCustomerTable();
    }

    public void addCustomer(Customer c){
        customer.add(c);
    }

    public void close(){
        connector.dropKeyspace("bank");
    }
}