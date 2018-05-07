package com.github.allprojects.consistencyTypes.exampleApplication;

import com.github.allprojects.consistencyTypes.cassandraInterface.CollectionWrapper;
import com.github.allprojects.consistencyTypes.cassandraInterface.Wrappable;

import java.util.HashSet;

public class Bank extends Wrappable {

    private BankConnector connector;
    private CollectionWrapper<HashSet<Wrappable>> customers;

    public Bank(BankConnector conn){
        this.connector = conn;
        this.customers = new CollectionWrapper<>(new HashSet<>());
        connector.createKeyspace("com/github/allprojects/consistencyTypes/exampleApplication", "SimpleStrategy", 1);
        connector.createCustomerTable();
    }

    public void addCustomer(Customer c){
        customers.add(c);
    }

    public void close(){
        connector.dropKeyspace("com/github/allprojects/consistencyTypes/exampleApplication");
    }
}