package de.tuda.stg.consys.demo.messagegroups;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.bench.BenchmarkUtils;
import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.demo.DemoRunnable;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.messagegroups.schema.Group;
import de.tuda.stg.consys.demo.messagegroups.schema.Inbox;
import de.tuda.stg.consys.demo.messagegroups.schema.User;
import de.tuda.stg.consys.japi.Ref;
import scala.Option;

import java.util.*;

/**
 * Created on 10.10.19.
 *
 * @author Mirko Köhler
 */
@SuppressWarnings({"consistency"})
public class MessageGroupsBenchmark extends DemoRunnable {
    public static void main(String[] args) {
        JBenchExecution.execute("message-groups", MessageGroupsBenchmark.class, args);
    }

    private final int numberOfUsersPerReplica;
    private final int numberOfGroupsPerReplica;

    private final List<Ref<Group>> groups;
    private final List<Ref<User>> users;

    public MessageGroupsBenchmark(JBenchStore adapter, BenchmarkConfig config) {
        super(adapter, config);

        numberOfUsersPerReplica = config.toConfig().getInt("consys.bench.demo.messagegroups.users");
        numberOfGroupsPerReplica = config.toConfig().getInt("consys.bench.demo.messagegroups.groups");

        users = new ArrayList<>(numberOfUsersPerReplica * config.numberOfReplicas());
        groups = new ArrayList<>(numberOfGroupsPerReplica * config.numberOfReplicas());
    }

    private static String addr(String identifier, int grpIndex, int replIndex) {
        return identifier + "$" + grpIndex + "$" + replIndex;
    }

    @Override
    public void setup() {
        System.out.println("Adding users");
        for (int userIndex = 0; userIndex < numberOfUsersPerReplica; userIndex++) {
            int finalUserIndex = userIndex;

            Ref<Inbox> inbox = (Ref<Inbox>) store().transaction(ctx -> Option.apply(
                    ctx.replicate(addr("inbox", finalUserIndex, processId()), getLevel(Inbox.class), Inbox.class))
            ).get();

            store().transaction(ctx -> {
                ctx.replicate(addr("user", finalUserIndex, processId()), getLevel(User.class), User.class,
                        addr("user", finalUserIndex, processId()), inbox);
                return Option.apply(0);
            });
            BenchmarkUtils.printProgress(userIndex);
        }

        for (int grpIndex = 0; grpIndex < numberOfGroupsPerReplica; grpIndex++) {
            int finalGrpIndex = grpIndex;

            store().transaction(ctx -> {
                ctx.replicate(addr("group", finalGrpIndex, processId()), getLevel(Group.class), Group.class);
                return Option.apply(0);
            });
            BenchmarkUtils.printProgress(grpIndex);
        }
        BenchmarkUtils.printDone();

        barrier("objects_added");

        for (int replIndex = 0; replIndex < nReplicas; replIndex++) {
            int finalReplIndex = replIndex;

            for (int grpIndex = 0; grpIndex < numberOfGroupsPerReplica; grpIndex++) {
                int finalGrpIndex = grpIndex;

                Ref<Group> group = (Ref<Group>) store().transaction(ctx -> Option.apply(
                        ctx.lookup(addr("group", finalGrpIndex, finalReplIndex), getLevel(Group.class), Group.class))
                ).get();
                groups.add(group);
            }

            for (int userIndex = 0; userIndex < numberOfUsersPerReplica; userIndex++) {
                int finalUserIndex = userIndex;

                Ref<User> user = (Ref<User>) store().transaction(ctx -> Option.apply(
                        ctx.lookup(addr("user", finalUserIndex, finalReplIndex), getLevel(User.class), User.class))
                ).get();
                users.add(user);

                // every user starts in one group
                if (replIndex == processId()) {
                    store().transaction(ctx -> {
                        try {
                            getRandomElement(groups).ref().addUser(user);
                        } catch (IllegalArgumentException ignored) {}
                        return Option.apply(0);
                    });
                }
            }
            BenchmarkUtils.printProgress(replIndex);
        }
        BenchmarkUtils.printDone();
    }

    private <T> ConsistencyLevel getLevel(Class<T> clazz) {
        switch (benchType) {
            case WEAK: return getWeakLevel();
            case STRONG: return getStrongLevel();
            case OP_MIXED: return getMixedLevel();
            case MIXED:
                if (clazz == Inbox.class || clazz == User.class)
                    return getWeakLevel();
                else if (clazz == Group.class)
                    return getStrongLevel();
                else
                    throw new UnsupportedOperationException("unknown replicated object type");
            default: throw new UnsupportedOperationException("unknown bench type");
        }
    }

    @Override
    public void cleanup() {
        groups.clear();
        users.clear();
    }

    @Override
    public void test() {
        if (processId() != 0) return;
        printTestResult();
    }

    @Override
    public BenchmarkOperations operations() {
        return BenchmarkOperations.withZipfDistribution(new Runnable[] {
                this::checkInbox,
                this::postMessage,
                this::joinGroup
        });
    }

    private void postMessage() {
        Ref<Group> group = getRandomElement(groups);

        store().transaction(ctx -> {
            group.ref().postMessage("Hello");
            return Option.apply(0);
        });
    }

    private void checkInbox() {
        Ref<User> user = getRandomElement(users);

        store().transaction(ctx -> {
            List<String> inbox = user.ref().getInbox();
            return Option.apply(0);
        });
    }

    private void joinGroup() {
        Ref<Group> group = getRandomElement(groups);
        Ref<User> user = getRandomElement(users);

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
                    check("user was added", prevGroupSize + 1 == group.ref().getUsers().size());
                else
                    check("capacity was respected", capacity == group.ref().getUsers().size());
                return Option.apply(0);
            });
        }
    }
}
