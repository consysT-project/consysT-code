package de.tu_darmstadt.consistency_types.example;

import de.tu_darmstadt.consistency_types.cassandra.ConsistentCassandraConnector;

public class BankConnector extends ConsistentCassandraConnector {

    private final String customerTableName = "customers";
    private final String idKey = "id";
    private final String nameKey = "name";
    private final String amountKey = "amount";
    private final String loyaltyKey = "loyalty";

    public BankConnector(){

    }

    public void createCustomerTable(){
        getSession().execute("CREATE TABLE IF NOT EXISTS " + customerTableName + " (" +
                idKey +" uuid primary key, " +
                nameKey + " varchar, "+
                amountKey +" int, " +
                loyaltyKey + " int);");
    }
}
