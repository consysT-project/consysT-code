import com.datastax.driver.core.*;
import com.github.allprojects.consistencyTypes.qual.High;

import com.datastax.driver.core.querybuilder.QueryBuilder;

public class BankConnector extends ConsistentCassandraConnector {

    @High private final String customerTableName = "customers";
    @High private final String idKey = "id";
    @High private final String nameKey = "name";
    @High private final String amountKey = "amount";

    public BankConnector(){

    }

    public void createCustomerTable(){
        getSession().execute("CREATE TABLE " + customerTableName + " ("+ idKey +" int primary key, "+ nameKey + " varchar, "+ amountKey +" int);");
    }

    public void addCustomer(@High Customer c){
        @SuppressWarnings("consistency")
        @High Statement query = QueryBuilder.insertInto(customerTableName).values(new String[] { idKey, nameKey, amountKey }, new Object[] { c.id, c.name.value(), c.amount.value() });
        this.executeAll(query);
    }
}
