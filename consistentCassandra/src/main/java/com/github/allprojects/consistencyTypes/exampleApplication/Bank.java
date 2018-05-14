package com.github.allprojects.consistencyTypes.exampleApplication;

import com.github.allprojects.consistencyTypes.cassandraInterface.CollectionWrapper;
import com.github.allprojects.consistencyTypes.cassandraInterface.ConsistencyObject;

import java.util.HashSet;

public class Bank extends ConsistencyObject {

    private BankConnector connector;
    private CollectionWrapper<HashSet<ConsistencyObject>> customers;

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