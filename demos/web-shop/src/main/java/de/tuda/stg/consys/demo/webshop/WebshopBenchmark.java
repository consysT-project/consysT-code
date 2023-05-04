package de.tuda.stg.consys.demo.webshop;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.bench.BenchmarkUtils;
import de.tuda.stg.consys.demo.DemoRunnable;
import de.tuda.stg.consys.demo.DemoUtils;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.webshop.schema.datacentric.MyProduct;
import de.tuda.stg.consys.demo.webshop.schema.datacentric.User;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import de.tuda.stg.consys.logging.Logger;
import scala.Option;

import java.util.ArrayList;
import java.util.List;

@SuppressWarnings({"consistency"})
public class WebshopBenchmark extends DemoRunnable {
    public static void main(String[] args) {
        JBenchExecution.execute("web-shop", WebshopBenchmark.class, args);
    }

    private static final int maxPrice = 100;
    private static final int initialMoney = 10000;
    private static final int maxQuantity = 150;
    private int numOfUsersPerReplica;
    private final List<Session> localSessions;

    private final List<Ref<? extends User>> users;
    private final List<Ref<? extends MyProduct>> products;


    public WebshopBenchmark(JBenchStore adapter, BenchmarkConfig config) {
        super(adapter, config);

        localSessions = new ArrayList<>();
        users = new ArrayList<>();
        products = new ArrayList<>();

        numOfUsersPerReplica = config.toConfig().getInt("consys.bench.demo.webshop.users");

        Session.userConsistencyLevel = getLevelWithMixedFallback(getMixedLevel());
        Session.productConsistencyLevel = getLevelWithMixedFallback(getMixedLevel());
    }

    private int getRandomPrice() {
        return random.nextInt() * maxPrice;
    }

    private int getRandomQuantity() {
        return random.nextInt() * maxQuantity;
    }

    @Override
    public void setup() {
        Logger.debug(procName(), "Creating objects");

        for (int userIndex = 0; userIndex < numOfUsersPerReplica; userIndex++) {
            var session = new Session((CassandraStoreBinding) store());
            localSessions.add(session);

            session.initUser(DemoUtils.addr("user", userIndex, processId()), DemoUtils.generateRandomName(), initialMoney);

            session.setBalance(10000);

            session.initProduct(DemoUtils.addr("product", userIndex, processId()),
                    DemoUtils.generateRandomText(1), DemoUtils.generateRandomText(10),
                    getRandomPrice(), getRandomQuantity());

            BenchmarkUtils.printProgress(userIndex);
        }

        barrier("users_added");

        Logger.debug(procName(), "Collecting objects");

        for (int userIndex = 0; userIndex < numOfUsersPerReplica; userIndex++) {
            for (int replicaIndex = 0; replicaIndex < nReplicas; replicaIndex++) {
                users.add(localSessions.get(0).findUser(DemoUtils.addr("user", userIndex, replicaIndex)));
                products.add(localSessions.get(0).findProduct(DemoUtils.addr("product", userIndex, replicaIndex)));
            }
        }


        BenchmarkUtils.printDone();
    }

    @Override
    public void cleanup() {
        localSessions.clear();
        users.clear();
        products.clear();
    }

    @Override
    public BenchmarkOperations operations() {
        return BenchmarkOperations.withZipfDistribution(new Runnable[] {
                this::buyProduct,
                this::listProducts,
                this::checkBalance,
        });
    }

    private void checkBalance() {
        Ref<? extends User> user = DemoUtils.getRandomElement(users);

        store().transaction(ctx -> {
            user.ref().getMoney();
            return Option.apply(0);
        });
    }

    private void listProducts() {
        Session session = DemoUtils.getRandomElement(localSessions);
        String[] replIds = new String[5];
        for (int i = 0; i < 5; i++) {
            int userIndex = random.nextInt(numOfUsersPerReplica);
            int replicaIndex = random.nextInt(nReplicas);
            replIds[i] = DemoUtils.addr("product", userIndex, replicaIndex);
        }
        session.browseProductsByReplIds(replIds);
    }

    private void buyProduct() {
        Session session = DemoUtils.getRandomElement(localSessions);

        store().transaction(ctx ->
        {
            var product = (Ref<MyProduct>) DemoUtils.getRandomElement(products);

            try {
                session.buyProduct(product, 1);
                return Option.apply(0);
            } catch (IllegalArgumentException e) {
                System.err.println("Exception raised by app: " + e.getMessage());
                return Option.apply(e);
            }
        });
    }

}
