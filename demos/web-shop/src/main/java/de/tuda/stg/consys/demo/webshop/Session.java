package de.tuda.stg.consys.demo.webshop;

import de.tuda.stg.consys.checker.qual.Immutable;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
//import de.tuda.stg.consys.demo.webshop.schema.opcentric.MyProduct;
import de.tuda.stg.consys.demo.webshop.schema.datacentric.MyProduct;
//import de.tuda.stg.consys.demo.webshop.schema.opcentric.User;
import de.tuda.stg.consys.demo.webshop.schema.datacentric.User;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;
import scala.Function1;
import scala.Option;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

import static de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.*;

@SuppressWarnings({"consistency"})
public class Session {
    private CassandraStoreBinding store;
    private List<Ref<MyProduct>> products;
    private Ref<User> user;
    public static ConsistencyLevel<CassandraStore> productConsistencyLevel = STRONG;
    public static ConsistencyLevel<CassandraStore> userConsistencyLevel = STRONG;
    private static ExecutorService threadPool;

    private <U> Option<U> doTransaction(Function1<CassandraTransactionContextBinding, Option<U>> code) {
        return store.transaction(code::apply);
    }

    public Session(@Mutable CassandraStoreBinding store) {
        this.store = store;
        this.products = new ArrayList<>();
        threadPool = Executors.newFixedThreadPool(1);
    }

    public void initProducts() {
        Ref<MyProduct> product = doTransaction(
                ctx -> Option.apply(ctx.replicate("bread", productConsistencyLevel, MyProduct.class, "Bread", "Great taste", 10, 20))).get();

        Ref<MyProduct> product2 = doTransaction(
                ctx -> Option.apply(ctx.replicate("milk", productConsistencyLevel, MyProduct.class, "Milk", "Healthy", 5, 20))).get();

        Ref<MyProduct> product3 = doTransaction(
                ctx -> Option.apply(ctx.replicate("cheese", productConsistencyLevel, MyProduct.class, "Cheese", "Smells good", 30, 20))).get();

        products.add(product);
        products.add(product2);
        products.add(product3);
    }

    public void initProduct(String id, String name, String description, int price, int quantity) {
        Ref<MyProduct> product = doTransaction(
                ctx -> Option.apply(ctx.replicate("product:" + id, productConsistencyLevel, MyProduct.class, name, description, price, quantity))).get();
        products.add(product);
    }

    public Ref<? extends @Mutable MyProduct> findProduct(String id) {
        return doTransaction(ctx -> Option.apply(ctx.lookup("product:" + id, productConsistencyLevel, MyProduct.class))).get();
    }

    public void initUser() {
        this.user = doTransaction(
                ctx -> Option.apply(ctx.replicate("user", userConsistencyLevel, User.class, "Name", 1000))).get();
    }

    public void initUser(String id, String name, int money) {
        this.user = doTransaction(
                ctx -> Option.apply(ctx.replicate("user:" + id, userConsistencyLevel, User.class, name, money))).get();
    }

    public Ref<? extends @Mutable User> findUser(String id) {
        return doTransaction(ctx -> Option.apply(ctx.lookup("user:" + id, userConsistencyLevel, User.class))).get();
    }

    public void setBalance(@Strong int amount) {
        doTransaction(ctx -> {
            user.ref().setBalance(amount);
            return Option.apply(0);
        });
    }

    public String browseProductsByReplIds(String[] replIds) {

        return doTransaction(ctx -> {
            var sb = new StringBuilder();
            @Immutable List<Ref<? extends MyProduct>> products = new ArrayList<>(replIds.length);
            for (String replId : replIds) {
                products.add(findProduct(replId));
            }

            sb.append("Products:\n");
            for (Ref<? extends MyProduct> product : products) {
                sb.append(product.ref().toString()).append("\n");
            }
            return Option.apply(sb.toString());
        }).get();
    }

    public void showProducts() {
        String productsString = doTransaction(ctx -> {
            var sb = new StringBuilder();
            System.out.printf("\u001B[32m%-22s%-22s%-22s%-22s\n", "NAME", "DESCRIPTION", "PRICE", "QUANTITY \u001B[0m");

            for (int i = 0; i < products.size(); i++) {
                String name = products.get(i).ref().getName();
                String desc = products.get(i).ref().getDescription();
                int price = products.get(i).ref().getPrice();
                int quantity = products.get(i).ref().getQuantity();

                System.out.printf("%-22s%-22s%-22s%-22s\n", name, desc, price, quantity);
            }

            return Option.apply(sb.toString());
        }).get();

        System.out.print(productsString);
    }

    public void showBalance() {
        String balanceString = doTransaction(ctx -> Option.apply(user.ref().toString())).get();
        System.out.print(balanceString);
    }

    public void buyProduct(String name, int amount) {
        boolean buy = doTransaction(ctx -> {
            Ref<MyProduct> product = ctx.lookup(name.toLowerCase(), productConsistencyLevel, MyProduct.class);
            boolean buySuccess = user.ref().buyProduct(product, amount);
            return Option.apply(buySuccess);
        }).get();

        if (buy) {
            System.out.println("Successfully bought " + amount + " of " + name + ".");
        }
        else {
            System.out.println("Could not buy " + amount + " of " + name + ". Either your balance is too low or product is not available in this quantity.");
        }
    }

    public void buyProduct(Ref<MyProduct> product, int amount) {
        doTransaction(ctx -> {
            user.ref().buyProduct(product, amount);
            return Option.apply(0);
        }).get();
    }
}
