import com.datastax.driver.core.*;
import com.datastax.driver.core.querybuilder.QueryBuilder;
import com.github.allprojects.consistencyTypes.qual.High;
import com.github.allprojects.consistencyTypes.qual.Low;

import static com.datastax.driver.core.querybuilder.QueryBuilder.eq;

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

    public void addCustomer(Customer c){
        @High Statement query = QueryBuilder.insertInto(customerTableName).values(new String[] { idKey, nameKey, amountKey }, new Object[] { c.id, c.name.value(), c.amount.value() });
        this.executeAll(query);
    }
}
