package de.tudarmstadt.consistency.demo.legacy.example;

import de.tudarmstadt.consistency.demo.legacy.CollectionWrapper;
import de.tudarmstadt.consistency.demo.legacy.ConsistencyObject;

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