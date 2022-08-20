package de.tuda.stg.consys.demo.messagegroups;

import com.typesafe.config.Config;
import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.bench.OutputFileResolver;
import de.tuda.stg.consys.demo.CassandraDemoBenchmark;
import de.tuda.stg.consys.bench.BenchmarkUtils;
import de.tuda.stg.consys.demo.messagegroups.schema.Group;
import de.tuda.stg.consys.demo.messagegroups.schema.Inbox;
import de.tuda.stg.consys.demo.messagegroups.schema.User;
import de.tuda.stg.consys.japi.Ref;
import scala.Option;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

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

    private final int numOfGroupsPerReplica;

    private final List<Ref<Group>> groups;
    private final List<Ref<User>> users;

    private final Random random = new Random();

    public MessageGroupsBenchmark(Config config, Option<OutputFileResolver> outputResolver) {
        super(config, outputResolver);

        numOfGroupsPerReplica = config.getInt("consys.bench.demo.messagegroups.groups");

        groups = new ArrayList<>(numOfGroupsPerReplica * nReplicas());
        users = new ArrayList<>(numOfGroupsPerReplica * nReplicas());
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
        for (int grpIndex = 0; grpIndex <= numOfGroupsPerReplica; grpIndex++) {
            int finalGrpIndex = grpIndex;

            store().transaction(ctx -> {
                ctx.replicate(addr("group", finalGrpIndex, processId()), getStrongLevel(), Group.class);
                return Option.apply(0);
            });

            Ref<Inbox> inbox = store().transaction(ctx -> Option.apply(
                    ctx.replicate(addr("inbox", finalGrpIndex, processId()), getWeakLevel(), Inbox.class))
            ).get();

            store().transaction(ctx -> {
                ctx.replicate(addr("user", finalGrpIndex, processId()), getWeakLevel(), User.class,
                        addr("alice", finalGrpIndex, processId()), inbox);
                return Option.apply(0);
            });

            BenchmarkUtils.printProgress(grpIndex);
        }
        BenchmarkUtils.printDone();

        barrier("users_added");

        for (int grpIndex = 0; grpIndex <= numOfGroupsPerReplica; grpIndex++) {
            for (int replIndex = 0; replIndex < nReplicas(); replIndex++) {
                int finalGrpIndex = grpIndex;
                int finalReplIndex = replIndex;

                Ref<Group> group;

                group = store().transaction(ctx -> Option.apply(
                        ctx.lookup(addr("group", finalGrpIndex, finalReplIndex), getWeakLevel(), Group.class))
                ).get();

                Ref<User> user = store().transaction(ctx -> Option.apply(
                        ctx.lookup(addr("user", finalGrpIndex, finalReplIndex), getWeakLevel(), User.class))
                ).get();

                // every group starts with one user
                if (replIndex == processId()) {
                    store().transaction(ctx -> {
                        group.ref().addUser(user);
                        return Option.apply(0);
                    });
                }

                groups.add(group);
                users.add(user);
            }
            BenchmarkUtils.printProgress(grpIndex);
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
        randomTransaction();
        System.out.print(".");
    }

    private List<Double> zipf(int n, double s) {
        double e = 0;
        for (int i = 1; i < n + 1; i++) {
            e += 1 / Math.pow(i, s);
        }

        List<Double> result = new ArrayList<>(n);
        for (int k = 1; k < n + 1; k++) {
            double z = (1 / Math.pow(k, s)) / e;
            double sum = result.isEmpty() ? z : result.get(result.size() - 1) + z;
            result.add(sum);
        }

        return result;
    }

    private void randomTransaction() {
        int rand = random.nextInt(100);
        if (rand < 58) /*12*/ {
            checkInbox();
        } else if (rand < 80) {
            postMessage();
        } else {
            joinGroup();
        }
        //user creation: left out
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

        store().transaction(ctx -> {
            group.ref().addUser(user);
            return Option.apply(0);
        });
    }
}
