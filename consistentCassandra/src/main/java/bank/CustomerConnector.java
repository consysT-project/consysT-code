package bank;

import cassandra.ConsistentCassandraConnector;
import com.datastax.driver.core.Statement;
import com.datastax.driver.core.querybuilder.QueryBuilder;
import com.github.allprojects.consistencyTypes.qual.High;

import static com.datastax.driver.core.querybuilder.QueryBuilder.eq;

public class CustomerConnector extends ConsistentCassandraConnector {

    private final String customerTableName = "customers";
    private final String idKey = "id";
    private final String nameKey = "name";
    private final String amountKey = "amount";


    @High private Statement getQuery(Customer c) {
        @SuppressWarnings("consistency")
        @High Statement query = QueryBuilder.select().from(customerTableName).where(eq(idKey, c.id));
        return query;
    }

    public void setBalance(Customer c, int balance) {
        @SuppressWarnings("consistency")
        @High Statement query = QueryBuilder.update(customerTableName).where(eq(idKey, c.id)).with(QueryBuilder.set(amountKey, balance));
        c.amount.execute(query);
    }

    public void withdraw(Customer c, int amount) {
        @SuppressWarnings("consistency")
        @High Statement query = QueryBuilder.select().from(customerTableName).where(eq(idKey, c.id));
        int balance = c.amount.execute(query).one().getInt(amountKey);
        setBalance(c,balance - amount);
    }

    @High public int getBalance(Customer c){
        return c.amount.execute(getQuery(c)).one().getInt(amountKey);
    }

    public String getName(Customer c) {
        return c.name.execute(getQuery(c)).one().getString(nameKey);
    }

    public void setName(Customer c, String name) {
        @SuppressWarnings("consistency")
        @High Statement query = QueryBuilder.update(customerTableName).where(eq(idKey, c.id)).with(QueryBuilder.set(nameKey, name));
        c.name.execute(query);
    }
}
