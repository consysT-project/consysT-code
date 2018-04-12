import com.datastax.driver.core.*;
import com.datastax.driver.core.querybuilder.Assignment;
import com.github.allprojects.consistencyTypes.qual.High;
import com.github.allprojects.consistencyTypes.qual.Low;

import com.datastax.driver.core.querybuilder.QueryBuilder;

import static com.datastax.driver.core.querybuilder.QueryBuilder.eq;

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
        @High Statement query = QueryBuilder.insertInto(customerTableName).values(new String[] { idKey, nameKey, amountKey }, new Object[] { c.id, c.name, c.amount });
        this.executeAll(query);
    }

    public void withdraw(@High Customer c, @High int amount){
        @SuppressWarnings("consistency")
        @High Statement query = QueryBuilder.select().from(customerTableName).where(eq(idKey, c.id));
        @SuppressWarnings("consistency")
        @High int balance = this.executeAll(query).one().getInt(amountKey);
        @SuppressWarnings("consistency")
        @High Assignment assignment = QueryBuilder.set(amountKey, balance - amount);
        QueryBuilder.update(customerTableName).where(eq(idKey, c.id)).with(assignment);
        this.executeAll(query);
    }

    public int getBalance(Customer c){
        @Low Statement query = QueryBuilder.select().from(customerTableName).where(eq(idKey, c.id));
        return this.executeSingle(query).one().getInt(amountKey);
    }
}
