package de.tuda.stg.consys.demo.webshop;

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

import static de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.WEAK;

public class Session {
    private CassandraStoreBinding store;
    private List<Ref<MyProduct>> products;
    private Ref<User> user;
    public static ConsistencyLevel<CassandraStore> productConsistencyLevel = WEAK;
    public static ConsistencyLevel<CassandraStore> userConsistencyLevel = WEAK;

    private <U> Option<U> doTransaction(Function1<CassandraTransactionContextBinding, Option<U>> code) {
        return store.transaction(code::apply);
    }

    public Session(@Mutable CassandraStoreBinding store) {
        this.store = store;
        this.products = new ArrayList<>();
    }

    public void initProducts() {
        Ref<MyProduct> product = doTransaction(
                ctx -> Option.apply(ctx.replicate("bread", productConsistencyLevel, MyProduct.class, "Bread", "Great taste", 10, 5))).get();

        Ref<MyProduct> product2 = doTransaction(
                ctx -> Option.apply(ctx.replicate("milk", productConsistencyLevel, MyProduct.class, "Milk", "Healthy", 5, 10))).get();

        Ref<MyProduct> product3 = doTransaction(
                ctx -> Option.apply(ctx.replicate("cheese", productConsistencyLevel, MyProduct.class, "Cheese", "Smells good", 30, 15))).get();

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
            sb.append("Available products: \n");
            for (int i = 0; i < products.size(); i++) {
                sb.append("=== \n");
                sb.append(products.get(i).ref().toString());
            }
            return Option.apply(sb.toString());
        }).get();

        System.out.println(productsString);
    }

    public void showBalance() {
        String balanceString = doTransaction(ctx -> Option.apply(user.ref().toString())).get();

        System.out.println(balanceString);
    }

    public void buyProduct(String name, int amount) {
        Ref<MyProduct> product = doTransaction(ctx ->
                Option.apply(ctx.lookup(name.toLowerCase(), productConsistencyLevel, MyProduct.class))).get();

        doTransaction(ctx -> {
            user.ref().buyProduct(product, amount);
            return Option.empty();
        });
    }

}
