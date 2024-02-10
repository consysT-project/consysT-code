package de.tuda.stg.consys.demo.messagegroups;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.bench.BenchmarkUtils;
import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.demo.DemoRunnable;
import de.tuda.stg.consys.demo.DemoUtils;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.messagegroups.schema.Group;
import de.tuda.stg.consys.demo.messagegroups.schema.Inbox;
import de.tuda.stg.consys.demo.messagegroups.schema.User;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.Store;
import de.tuda.stg.consys.japi.TransactionContext;
import de.tuda.stg.consys.logging.Logger;
import scala.Function1;
import scala.Option;

import java.io.Serializable;
import java.util.*;
import java.util.concurrent.TimeoutException;

/**
 * Created on 10.10.19.
 *
 * @author Mirko Köhler
 */
@SuppressWarnings({"consistency"})
public class MessageGroupsBenchmark<SStore extends de.tuda.stg.consys.core.store.Store>
        extends DemoRunnable<String, Serializable, TransactionContext<String, Serializable, ConsistencyLevel<SStore>>, Store<String, Serializable, ConsistencyLevel<SStore>, TransactionContext<String, Serializable, ConsistencyLevel<SStore>>>, SStore>{
    public static void main(String[] args) {
        JBenchExecution.execute("message-groups", MessageGroupsBenchmark.class, args);
    }

    private final int nMaxRetries;
    private final int retryDelay;

    private final int numberOfUsersPerReplica;
    private final int numberOfGroupsPerReplica;

    private final List<Ref<Group>> groups;
    private final List<Ref<User>> users;

    public MessageGroupsBenchmark(
            JBenchStore<String, Serializable, TransactionContext<String, Serializable, ConsistencyLevel<SStore>>, Store<String, Serializable,
                    ConsistencyLevel<SStore>,
                    TransactionContext<String, Serializable, ConsistencyLevel<SStore>>>, SStore
                    > adapter,
            BenchmarkConfig config) {
        super(adapter, config);

        numberOfUsersPerReplica = config.toConfig().getInt("consys.bench.demo.messagegroups.users");
        numberOfGroupsPerReplica = config.toConfig().getInt("consys.bench.demo.messagegroups.groups");

        nMaxRetries = config.toConfig().getInt("consys.bench.demo.messagegroups.retries");
        retryDelay = config.toConfig().getInt("consys.bench.demo.messagegroups.retryDelay");

        users = new ArrayList<>(numberOfUsersPerReplica * config.numberOfReplicas());
        groups = new ArrayList<>(numberOfGroupsPerReplica * config.numberOfReplicas());

        switch (benchType) {
            case STRONG_DATACENTRIC:
            case WEAK_DATACENTRIC:
                throw new IllegalArgumentException("STRONG_DATACENTRIC, WEAK_DATACENTRIC not supported by message-groups bench");
        }
    }

    @Override
    public void setup() {
        Logger.debug("Creating objects");
        for (int userIndex = 0; userIndex < numberOfUsersPerReplica; userIndex++) {
            int finalUserIndex = userIndex;

            Ref<Inbox> inbox = store().transaction(ctx -> Option.apply(
                    ctx.replicate(DemoUtils.addr("inbox", finalUserIndex, processId()), getLevelWithMixedFallback(getWeakLevel()), Inbox.class))
            ).get();

            store().transaction(ctx -> {
                ctx.replicate(DemoUtils.addr("user", finalUserIndex, processId()), getLevelWithMixedFallback(getWeakLevel()), User.class,
                        DemoUtils.addr("user", finalUserIndex, processId()), inbox);
                return Option.apply(0);
            });
            BenchmarkUtils.printProgress(userIndex);
        }

        for (int grpIndex = 0; grpIndex < numberOfGroupsPerReplica; grpIndex++) {
            int finalGrpIndex = grpIndex;

            store().transaction(ctx -> {
                ctx.replicate(DemoUtils.addr("group", finalGrpIndex, processId()), getLevelWithMixedFallback(getStrongLevel()), Group.class);
                return Option.apply(0);
            });
            BenchmarkUtils.printProgress(grpIndex);
        }
        BenchmarkUtils.printDone();

        barrier("objects_added");

        Logger.debug("Collecting objects");
        for (int replIndex = 0; replIndex < nReplicas; replIndex++) {
            int finalReplIndex = replIndex;

            for (int grpIndex = 0; grpIndex < numberOfGroupsPerReplica; grpIndex++) {
                int finalGrpIndex = grpIndex;

                Ref<Group> group = store().transaction(ctx -> Option.apply(
                        ctx.lookup(DemoUtils.addr("group", finalGrpIndex, finalReplIndex), getLevelWithMixedFallback(getStrongLevel()), Group.class))
                ).get();
                groups.add(group);
            }

            for (int userIndex = 0; userIndex < numberOfUsersPerReplica; userIndex++) {
                int finalUserIndex = userIndex;

                Ref<User> user = store().transaction(ctx -> Option.apply(
                        ctx.lookup(DemoUtils.addr("user", finalUserIndex, finalReplIndex), getLevelWithMixedFallback(getWeakLevel()), User.class))
                ).get();
                users.add(user);

                // every user starts in one group
                if (replIndex == processId()) {
                    store().transaction(ctx -> {
                        try {
                            DemoUtils.getRandomElement(groups).ref().addUser(user);
                        } catch (IllegalArgumentException ignored) {}
                        return Option.apply(0);
                    });
                }
            }
            BenchmarkUtils.printProgress(replIndex);
        }
        BenchmarkUtils.printDone();
    }

    @Override
    public void cleanup() {
        groups.clear();
        users.clear();
    }

    @Override
    public void test() {
        if (processId() == 0) printTestResult();
    }

    @Override
    public BenchmarkOperations operations() {
        return BenchmarkOperations.withZipfDistribution(new Runnable[] {
                this::checkInbox,
                this::postMessage,
                this::joinGroup
        });
    }

    private <U> Option<U> withRetry(Function1<TransactionContext<String, Serializable, ConsistencyLevel<SStore>>, Option<U>> code) {
        int nTries = 0;
        while (true) {
            try {
                return store().transaction(code::apply);
            } catch (Exception e) {
                if (!(e instanceof TimeoutException)) throw e;
                Logger.warn("Timeout during operation. Retrying...");
                nTries++;
                try { Thread.sleep(random.nextInt(retryDelay)); } catch (InterruptedException ignored) {}
                if (nTries > nMaxRetries) {
                    Logger.err("Timeout during operation. Max retries reached.");
                    throw e;
                }
            }
        }
    }

    private void postMessage() {
        Ref<Group> group = DemoUtils.getRandomElement(groups);

        withRetry(ctx -> {
            group.ref().postMessage("Hello");
            return Option.apply(0);
        });
    }

    private void checkInbox() {
        Ref<User> user = DemoUtils.getRandomElement(users);

        store().transaction(ctx -> {
            List<String> inbox = user.ref().getInbox();
            return Option.apply(0);
        });
    }

    private void joinGroup() {
        Ref<Group> group = DemoUtils.getRandomElement(groups);
        Ref<User> user = DemoUtils.getRandomElement(users);

        Option<Integer> result = store().transaction(ctx -> {
            int groupSize = isTestMode ? group.ref().getUsers().size() : -1;

            try {
                group.ref().addUser(user);
            } catch (IllegalArgumentException ignored) {}

            return Option.apply(groupSize);
        });

        if (isTestMode) {
            store().transaction(ctx -> {
                int prevGroupSize = result.get();
                int capacity = group.ref().getCapacity();
                if (prevGroupSize < capacity)
                    check("user was added", prevGroupSize < group.ref().getUsers().size());
                check("capacity was respected", capacity >= group.ref().getUsers().size());
                return Option.apply(0);
            });
        }
    }
}
