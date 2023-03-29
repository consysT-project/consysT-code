package de.tuda.stg.consys.demo.rubis;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.bench.BenchmarkUtils;
import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.demo.*;
import de.tuda.stg.consys.demo.rubis.schema.*;
import de.tuda.stg.consys.japi.Store;
import de.tuda.stg.consys.japi.TransactionContext;
import de.tuda.stg.consys.logging.Logger;
import scala.Option;

import java.io.Serializable;
import java.util.*;

@SuppressWarnings({"consistency"})
public class RubisBenchmark<SStore extends de.tuda.stg.consys.core.store.Store>
        extends DemoRunnable<String, Serializable, TransactionContext<String, Serializable, ConsistencyLevel<SStore>>, Store<String, Serializable, ConsistencyLevel<SStore>, TransactionContext<String, Serializable, ConsistencyLevel<SStore>>>, SStore> {
    public static void main(String[] args) {
        JBenchExecution.execute("rubis", RubisBenchmark.class, args);
    }

    private static final float maxPrice = 100;

    private final int numOfUsersPerReplica;
    private final List<ISession<SStore>> localSessions;
    private final List<String> users;
    private final List<String> items;

    private int itemNoOps;
    private int itemOps;


    public RubisBenchmark(
            JBenchStore<String, Serializable, TransactionContext<String, Serializable, ConsistencyLevel<SStore>>, Store<String, Serializable,
                    ConsistencyLevel<SStore>,
                    TransactionContext<String, Serializable, ConsistencyLevel<SStore>>>, SStore
                    > adapter,
            BenchmarkConfig config) {
        super(adapter, config);
        localSessions = new ArrayList<>();
        users = new ArrayList<>();
        items = new ArrayList<>();

        numOfUsersPerReplica = config.toConfig().getInt("consys.bench.demo.rubis.users");

        ISession.nMaxRetries = config.toConfig().getInt("consys.bench.demo.rubis.retries");
        ISession.retryDelay = config.toConfig().getInt("consys.bench.demo.rubis.retryDelay");

        if (isOpCentricImpl()) {
            TestUtils.benchType = TestUtils.BenchType.OP_CENTRIC;
        } else {
            TestUtils.benchType = TestUtils.BenchType.DATA_CENTRIC;
        }
    }

    private Category getRandomCategory() {
        return Category.values()[random.nextInt(Category.values().length)];
    }

    private float getRandomPrice() {
        return random.nextFloat() * maxPrice;
    }

    protected float getInitialBalance() {
        return numOfUsersPerReplica * nReplicas * maxPrice * 1.3f;
    }

    @Override
    public void setup() {
        TestUtils.store = store();

        Logger.debug(procName(), "Creating objects");
        for (int userIndex = 0; userIndex < numOfUsersPerReplica; userIndex++) {

            ISession<SStore> session;
            if (isOpCentricImpl()) {
                session = new de.tuda.stg.consys.demo.rubis.schema.opcentric.Session<>(store(),
                        getLevelWithMixedFallback(getStrongLevel()),
                        getLevelWithMixedFallback(getStrongLevel()));
            } else {
                session = new de.tuda.stg.consys.demo.rubis.schema.datacentric.Session<>(store(),
                        getLevelWithMixedFallback(getWeakLevel()),
                        getLevelWithMixedFallback(getWeakLevel()),
                        getLevelWithMixedFallback(getStrongLevel()));
            }

            localSessions.add(session);

            session.registerUser(null,
                    DemoUtils.addr("user", userIndex, processId()),
                    DemoUtils.addr("user", userIndex, processId()),
                    DemoUtils.generateRandomName(), DemoUtils.generateRandomPassword(), "mail@example.com");

            session.addBalance(null, getInitialBalance());

            session.registerItem(null,
                    DemoUtils.addr("item", userIndex, processId()),
                    DemoUtils.addr("item", userIndex, processId()), DemoUtils.generateRandomText(10),
                    getRandomCategory(), getRandomPrice(), 86400);

            BenchmarkUtils.printProgress(userIndex);
        }

        barrier("users_added");

        Logger.debug(procName(), "Collecting objects");
        for (int userIndex = 0; userIndex < numOfUsersPerReplica; userIndex++) {
            for (int replicaIndex = 0; replicaIndex < nReplicas; replicaIndex++) {
                users.add(DemoUtils.addr("user", userIndex, replicaIndex));
                items.add(DemoUtils.addr("item", userIndex, replicaIndex));
            }
        }

        BenchmarkUtils.printDone();
    }

    @Override
    public void cleanup() {
        Logger.info(procName(), "nops w.r.t auction operations: " + (float)itemNoOps/itemOps);
        Logger.info(procName(), "nops w.r.t all operations: " + (float)itemNoOps/100);

        localSessions.clear();
        users.clear();
        items.clear();
    }

    @Override
    public BenchmarkOperations operations() {
        return BenchmarkOperations.withZipfDistribution(new Runnable[] {
                withExceptionHandling(this::browseItems),
                withExceptionHandling(this::placeBid),
                withExceptionHandling(this::buyNow),
                withExceptionHandling(this::rateUser),
                withExceptionHandling(this::closeAuction)
        });
    }

    private Runnable withExceptionHandling(Runnable op) {
        return () -> {
            try {
                op.run();
            } catch (AppException e) {
                /* possible/acceptable errors:
                    - bidding on own item (rare)
                    - auction has already ended (common)
                */
                //System.err.println(e.getMessage());
            }
        };
    }

    private void placeBid() {
        var session = DemoUtils.getRandomElement(localSessions);

        store().transaction(ctx -> {
            var item = DemoUtils.getRandomElement(items);
            if (localSessions.get(0).getItemStatus(ctx, item) != ItemStatus.OPEN)
                itemNoOps++;
            itemOps++;

            float bid = session.getBidPrice(ctx, item);
            session.placeBid(ctx, item, bid * (1 + random.nextFloat()));
            return Option.apply(0);
        });
    }

    private void buyNow() {
        var session = DemoUtils.getRandomElement(localSessions);

        Option<TestUtils.TransactionResult> result = store().transaction(ctx ->
        {
            var item = DemoUtils.getRandomElement(items);
            if (session.getItemStatus(ctx, item) != ItemStatus.OPEN)
                itemNoOps++;
            itemOps++;

            var trxResult = !isTestMode
                    ? TestUtils.TransactionResult.empty()
                    : TestUtils.TransactionResult.empty()
                            .addUsers(session, session.getUser(), session.getItemSeller(ctx, item))
                            .addItems(session, item);

            try {
                session.buyNow(ctx, item);
                return Option.apply(trxResult);
            } catch (IllegalArgumentException e) {
                trxResult.appExceptions = new Exception[] { e };
                System.err.println("Exception raised by app: " + e.getMessage());
                return Option.apply(trxResult);
            }
        });

        if (isTestMode && result.isDefined()) {
            TestUtils.buyNowTest(result.get());
        }
    }

    private void closeAuction() {
        Option<TestUtils.TransactionResult> result = store().transaction(ctx ->
        {
            var item = DemoUtils.getRandomElement(items);
            if (localSessions.get(0).getItemStatus(ctx, item) != ItemStatus.OPEN)
                itemNoOps++;
            itemOps++;

            var trxResult = !isTestMode ? new TestUtils.TransactionResult() : new TestUtils.TransactionResult(
                    new TestUtils.UserTestInterface[] { new TestUtils.UserTestInterface(localSessions.get(0).getItemSeller(ctx, item), localSessions.get(0)) },
                    new TestUtils.ItemTestInterface[] { new TestUtils.ItemTestInterface(item, localSessions.get(0)) });

            try {
                localSessions.get(0).endAuctionImmediately(ctx, item);
            } catch (IllegalArgumentException e) {
                trxResult.appExceptions = new Exception[] { e };
                System.err.println("Exception raised by app: " + e.getMessage());
            }
            return Option.apply(trxResult);
        });

        if (isTestMode && result.isDefined()) {
            TestUtils.closeAuctionTest(result.get());
        }
    }

    private void browseItems() {
        var session = DemoUtils.getRandomElement(localSessions);
        String[] replIds = new String[5];
        for (int i = 0; i < 5; i++) {
            int userIndex = random.nextInt(numOfUsersPerReplica);
            int replicaIndex = random.nextInt(nReplicas);
            replIds[i] = DemoUtils.addr("item", userIndex, replicaIndex);
        }
        session.browseItemsByItemIds(null, replIds);
    }

    private void rateUser() {
        var session = DemoUtils.getRandomElement(localSessions);
        var user2 = DemoUtils.getRandomElementExcept(users, session.getUser());
        int rating = 1 + random.nextInt(5);
        session.rateUser(null, user2, rating, DemoUtils.generateRandomText(10));
    }

    @Override
    public void test() {
        if (processId() != 0) return;

        TestCollector.check("users non empty", !users.isEmpty());
        TestUtils.finalTest(users, getInitialBalance(), localSessions.get(0));

        printTestResult();
    }

    private boolean isOpCentricImpl() {
        switch (benchType) {
            case OP_MIXED:
            case WEAK:
            case STRONG:
            case DATACENTRIC_MIXED_IN_OPCENTRIC_IMPL:
                return true;
            case MIXED:
            case STRONG_DATACENTRIC:
            case WEAK_DATACENTRIC:
                return false;
        }

        throw new RuntimeException("unknown bench type");
    }
}
