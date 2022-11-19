package de.tuda.stg.consys.demo.webshop.extras;

import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.demo.webshop.schema.MyProduct;
import de.tuda.stg.consys.demo.webshop.schema.User;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;
import scala.Function1;
import scala.Option;
import scala.Tuple3;

import static de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.STRONG;
import static de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.WEAK;

public class BackgroundTask implements Runnable {
    private CassandraStoreBinding store;
    private boolean running = true;
    private final long sleepMilliseconds = 1000;
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

            Ref<MyProduct> product = doTransaction(ctx ->
                    Option.apply(ctx.lookup("milk", STRONG, MyProduct.class))).get();

            this.user = doTransaction(
                    ctx -> Option.apply(ctx.replicate("user", WEAK, User.class))).get();

            doTransaction(ctx -> {
                user.ref().buyProduct(product, 1);
                return Option.apply(user);
            });

            System.out.println("THREAD BUY");

            try {
                Thread.sleep(sleepMilliseconds);
            } catch (InterruptedException e) {
                return;
            }
        }
    }

    public void stopThread() {
        running = false;
    }


}
