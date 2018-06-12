package de.tudarmstadt.consistency.cassandra.legacy.example;

import de.tudarmstadt.consistency.cassandra.legacy.CollectionWrapper;
import de.tudarmstadt.consistency.cassandra.legacy.ConsistencyObject;

import java.util.HashSet;

public class Bank extends ConsistencyObject {

    private BankConnector connector;
    private CollectionWrapper<HashSet<ConsistencyObject>> customers;

    public Bank(BankConnector conn){
        this.connector = conn;
        this.customers = new CollectionWrapper<>(new HashSet<>());
        connector.createKeyspace("exampleApplication", "SimpleStrategy", 1);
        connector.createCustomerTable();
    }

    public void addCustomer(Customer c){
        customers.add(c);
    }

    public void close(){
        connector.dropKeyspace("exampleApplication");
    }
}