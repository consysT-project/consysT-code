package de.tudarmstadt.consistency.demo.legacy.example;

import com.datastax.driver.core.Statement;
import com.datastax.driver.core.querybuilder.QueryBuilder;
import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.demo.legacy.ConsistentCassandraConnector;

import static com.datastax.driver.core.querybuilder.QueryBuilder.eq;

public class CustomerConnector extends ConsistentCassandraConnector {

    private final String customerTableName = "customers";
    private final String idKey = "id";
    private final String nameKey = "name";
    private final String amountKey = "amount";
    private final String loyaltyKey = "loyalty";


    private Statement getQuery(Customer c) {
        return QueryBuilder.select().from(customerTableName).where(eq(idKey, c.id));
    }

    @Strong
    public int getBalance(Customer c){
        @SuppressWarnings("consistency")
        @Strong int balance = c.amount.execute(getQuery(c)).one().getInt(amountKey);
        return balance;
    }

    public void setBalance(Customer c, @Strong int balance) {
        Statement query = QueryBuilder.update(customerTableName).where(eq(idKey, c.id)).with(QueryBuilder.set(amountKey, balance));
        c.amount.execute(query);
    }

    @Strong
    public String getName(Customer c) {
        @SuppressWarnings("consistency")
        @Strong String name = c.name.execute(getQuery(c)).one().getString(nameKey);
        return name;
    }

    public void setName(Customer c, @Strong String name) {
        Statement query = QueryBuilder.update(customerTableName).where(eq(idKey, c.id)).with(QueryBuilder.set(nameKey, name));
        c.name.execute(query);
    }

    public int getLoyaltyPoints(Customer c){
        return c.loyaltyPoints.execute(getQuery(c)).one().getInt(loyaltyKey);

    }

    public void setLoyaltyPoints(Customer c, int loyalty) {
        c.loyaltyPoints.execute(QueryBuilder.update(customerTableName).where(eq(idKey, c.id)).with(QueryBuilder.set(loyaltyKey, loyalty)));
    }
}
