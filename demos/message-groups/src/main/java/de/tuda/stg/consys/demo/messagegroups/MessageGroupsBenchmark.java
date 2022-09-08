package de.tuda.stg.consys.demo.messagegroups;

import com.typesafe.config.Config;
import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.bench.BenchmarkUtils;
import de.tuda.stg.consys.bench.OutputResolver;
import de.tuda.stg.consys.demo.CassandraDemoBenchmark;
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
public class MessageGroupsBenchmark extends CassandraDemoBenchmark {
    public static void main(String[] args) {
        start(MessageGroupsBenchmark.class, args);
    }

    private final List<Runnable> operations = new ArrayList<>(Arrays.asList(
            this::checkInbox,
            this::postMessage,
            this::joinGroup
    ));

    private final List<Double> zipf;

    private final int numOfUsersPerReplica;
    private final int numOfGroupsPerReplica;

    private final List<Ref<Group>> groups;
    private final List<Ref<User>> users;

    public MessageGroupsBenchmark(Config config, Option<OutputResolver> outputResolver) {
        super(config, outputResolver);

        numOfUsersPerReplica = config.getInt("consys.bench.demo.messagegroups.users");
        numOfGroupsPerReplica = config.getInt("consys.bench.demo.messagegroups.groups");

        zipf = zipfSummed(operations.size());

        users = new ArrayList<>(numOfUsersPerReplica * nReplicas());
        groups = new ArrayList<>(numOfGroupsPerReplica * nReplicas());
    }

    private static String addr(String identifier, int grpIndex, int replIndex) {
        return identifier + "$" + grpIndex + "$" + replIndex;
    }

    @Override
    public String getName() {
        return "MessageGroupsBenchmark";
    }

    @Override
    public void setup() {
        super.setup();

        System.out.println("Adding users");
        for (int userIndex = 0; userIndex < numOfUsersPerReplica; userIndex++) {
            int finalUserIndex = userIndex;

            Ref<Inbox> inbox = store().transaction(ctx -> Option.apply(
                    ctx.replicate(addr("inbox", finalUserIndex, processId()), getWeakLevel(), Inbox.class))
            ).get();

            store().transaction(ctx -> {
                ctx.replicate(addr("user", finalUserIndex, processId()), getWeakLevel(), User.class,
                        addr("user", finalUserIndex, processId()), inbox);
                return Option.apply(0);
            });
            BenchmarkUtils.printProgress(userIndex);
        }

        for (int grpIndex = 0; grpIndex < numOfGroupsPerReplica; grpIndex++) {
            int finalGrpIndex = grpIndex;

            store().transaction(ctx -> {
                ctx.replicate(addr("group", finalGrpIndex, processId()), getStrongLevel(), Group.class);
                return Option.apply(0);
            });
            BenchmarkUtils.printProgress(grpIndex);
        }
        BenchmarkUtils.printDone();

        barrier("objects_added");

        for (int replIndex = 0; replIndex < nReplicas(); replIndex++) {
            int finalReplIndex = replIndex;

            for (int grpIndex = 0; grpIndex < numOfGroupsPerReplica; grpIndex++) {
                int finalGrpIndex = grpIndex;

                Ref<Group> group = store().transaction(ctx -> Option.apply(
                        ctx.lookup(addr("group", finalGrpIndex, finalReplIndex), getStrongLevel(), Group.class))
                ).get();
                groups.add(group);
            }

            for (int userIndex = 0; userIndex < numOfUsersPerReplica; userIndex++) {
                int finalUserIndex = userIndex;

                Ref<User> user = store().transaction(ctx -> Option.apply(
                        ctx.lookup(addr("user", finalUserIndex, finalReplIndex), getWeakLevel(), User.class))
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

    @Override
    public void cleanup() {
        super.cleanup();
        groups.clear();
        users.clear();
        try {
            Thread.sleep(1000);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }

    @Override
    public void operation() {
        randomTransaction(operations, zipf);
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
