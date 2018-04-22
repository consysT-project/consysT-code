package bank;

import cassandra.ConsistentCassandraConnector;
import com.datastax.driver.core.*;
import com.github.allprojects.consistencyTypes.qual.High;

import com.datastax.driver.core.querybuilder.QueryBuilder;

public class BankConnector extends ConsistentCassandraConnector {

    private final String customerTableName = "customers";
    private final String idKey = "id";
    private final String nameKey = "name";
    private final String amountKey = "amount";

    public BankConnector(){

    }

    public void createCustomerTable(){
        getSession().execute("CREATE TABLE " + customerTableName + " ("+ idKey +" int primary key, "+ nameKey + " varchar, "+ amountKey +" int);");
    }
}
