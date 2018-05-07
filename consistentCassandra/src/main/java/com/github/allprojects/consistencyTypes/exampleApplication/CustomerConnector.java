package com.github.allprojects.consistencyTypes.exampleApplication;

import com.datastax.driver.core.Statement;
import com.datastax.driver.core.querybuilder.QueryBuilder;
import com.github.allprojects.consistencyTypes.cassandraInterface.ConsistentCassandraConnector;
import com.github.allprojects.consistencyTypes.qual.High;

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

    @High public int getBalance(Customer c){
        @SuppressWarnings("consistency")
        @High int balance = c.amount.execute(getQuery(c)).one().getInt(amountKey);
        return balance;
    }

    public void setBalance(Customer c, @High int balance) {
        Statement query = QueryBuilder.update(customerTableName).where(eq(idKey, c.id)).with(QueryBuilder.set(amountKey, balance));
        c.amount.execute(query);
    }

    @High
    public String getName(Customer c) {
        @SuppressWarnings("consistency")
        @High String name = c.name.execute(getQuery(c)).one().getString(nameKey);
        return name;
    }

    public void setName(Customer c, @High String name) {
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
