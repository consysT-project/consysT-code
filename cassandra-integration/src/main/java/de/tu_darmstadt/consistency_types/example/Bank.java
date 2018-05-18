package de.tu_darmstadt.consistency_types.example;

import de.tu_darmstadt.consistency_types.cassandra.CollectionWrapper;
import de.tu_darmstadt.consistency_types.cassandra.ConsistencyObject;

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