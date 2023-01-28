package de.tuda.stg.consys.demo.webshop.extras;

import de.tuda.stg.consys.checker.qual.Immutable;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.demo.webshop.schema.datacentric.MyProduct;
import de.tuda.stg.consys.demo.webshop.schema.datacentric.User;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;
import scala.Function1;
import scala.Option;
import java.util.Random;

import static de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.*;

@SuppressWarnings({"consistency"})
public class BackgroundTask implements Runnable {
    private CassandraStoreBinding store;
    private boolean running = true;
    private Ref<User> user;

    private <U> Option<U> doTransaction(Function1<CassandraTransactionContextBinding, Option<U>> code) {
        return store.transaction(code::apply);
    }

    public BackgroundTask(@Mutable CassandraStoreBinding store) {
        this.store = store;
    }

    @Override
    public void run() {
        while (running) {
            @Immutable String randomProduct = getRandomProduct();
            int randomAmount = getRandomAmount();

            boolean buy = doTransaction(ctx -> {
                    Ref<MyProduct> product = ctx.lookup(randomProduct, STRONG, MyProduct.class);
                    this.user = ctx.lookup("user", STRONG, User.class);
                    boolean buySuccess = user.ref().buyProduct(product, randomAmount);

                    System.out.print("\u001B[35m [BACKGROUND TASK]: ");

                    if (buySuccess) {
                        System.out.println("Successfully bought " + randomAmount + " of " + randomProduct + ". \u001B[0m");
                    }
                    else {
                        System.out.println("Could not buy " + randomAmount + " of " + randomProduct + ". Either the balance is too low or product is not available in this quantity. \u001B[0m");
                    }

                return Option.apply(buySuccess);
            }).get();

            try {
                Thread.sleep(5000);
            } catch (InterruptedException e) {
                throw new RuntimeException(e);
            }
        }
    }

    private String getRandomProduct() {
        String[] availableProducts = {"milk", "cheese", "bread"};
        int rnd = new Random().nextInt(availableProducts.length);
        return availableProducts[rnd];
    }

    private int getRandomAmount() {
        return new Random().nextInt(10) + 1;
    }

    public void stopThread() {
        running = false;
    }


}
