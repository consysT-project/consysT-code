package bank;

import cassandra.ConsistentCassandraConnector;

public class BankConnector extends ConsistentCassandraConnector {

    private final String customerTableName = "customers";
    private final String idKey = "id";
    private final String nameKey = "name";
    private final String amountKey = "amount";
    private final String loyaltyKey = "loyalty";

    public BankConnector(){

    }

    public void createCustomerTable(){
        getSession().execute("CREATE TABLE " + customerTableName + " ("+
                idKey +" uuid primary key, " +
                nameKey + " varchar, "+
                amountKey +" int, " +
                loyaltyKey + " int);");
    }
}
