package de.tuda.stg.consys.demo.webshop;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.demo.webshop.schema.MyProduct;
import de.tuda.stg.consys.demo.webshop.schema.User;
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
    public static ConsistencyLevel<CassandraStore> productConsistencyLevel = MIXED;
    public static ConsistencyLevel<CassandraStore> userConsistencyLevel = MIXED;
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

    public void initUser() {
        this.user = doTransaction(
                ctx -> Option.apply(ctx.replicate("user", userConsistencyLevel, User.class))).get();
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

    public void runBalanceChecker() {
        threadPool.submit(new BalanceChecker());
    }

    public void stopBalanceChecker() {
        threadPool.shutdown();
    }

    class BalanceChecker implements Runnable {
        @Override
        public void run() {
            while (true) {

                int balanceLeft = doTransaction(ctx -> Option.apply(user.ref().getMoney())).get();
                if (balanceLeft < 800) {
                    System.out.println("\u001B[33m [USER WARNING]: Balance is less than 800. \u001B[0m");
                    break;
                }


                try {
                    Thread.sleep(8000);
                } catch (InterruptedException e) {
                    throw new RuntimeException(e);
                }
            }
        }
    }
}
