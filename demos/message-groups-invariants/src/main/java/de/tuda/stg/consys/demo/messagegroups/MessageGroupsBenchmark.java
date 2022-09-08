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

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.Set;

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

    public MessageGroupsBenchmark(Config config, Option<OutputResolver> outputResolver) {
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
            try {
                int finalGrpIndex = grpIndex;

                store().transaction(ctx -> {
                    ctx.replicate(addr("group", finalGrpIndex, processId()), getWeakLevel(), Group.class);
                    return Option.empty();
                });
                Thread.sleep(33);

                Ref<Inbox> inbox = store().transaction(ctx -> Option.apply(
                        ctx.replicate(addr("inbox", finalGrpIndex, processId()), getWeakLevel(), Inbox.class))
                ).get();
                Thread.sleep(33);

                store().transaction(ctx -> {
                    ctx.replicate(addr("user", finalGrpIndex, processId()), getWeakLevel(), User.class,
                            inbox, addr("alice", finalGrpIndex, processId()));
                    return Option.empty();
                });
                Thread.sleep(33);

                BenchmarkUtils.printProgress(grpIndex);
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
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

                if (replIndex == processId()) {
                    store().transaction(ctx -> {
                        // TODO: Change this
//                        group.addUser(user);
                        return Option.empty();
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
        store().transaction(ctx -> {
            randomTransaction();
           return Option.empty();
        });
        System.out.print(".");
    }

    @Transactional
    private int randomTransaction() {
        int rand = random.nextInt(100);
        if (rand < 58) /*12*/ {
            // inbox checking
            return transaction2();
        } else if (rand < 80) {
            // message posting
            return transaction1();
        } else if (rand < 100) {
            // group joining
            return transaction3();
        }
        //user creation: left out

        throw new IllegalStateException("cannot be here");
    }

    @Transactional
    private int transaction1() {
        int i = random.nextInt(groups.size());
        Ref<Group> group = groups.get(i);
        //   System.out.println(Thread.currentThread().getName() +  ": tx1 " + group);
        group.ref().addPost("Hello " + i);
        return 0;
    }

    @Transactional
    private int transaction2() {
        int i = random.nextInt(users.size());
        Ref<User> user = users.get(i);
        // System.out.println(Thread.currentThread().getName() + ": tx2 " + user);

        Set<String> inbox = user.ref().getInbox();

        return 1;
    }

    @Transactional
    private int transaction3() {
        int i = random.nextInt(groups.size());
        int j = random.nextInt(users.size());

        Ref<Group> group = groups.get(i);
        Ref<User> user = users.get(j);

        // System.out.println(Thread.currentThread().getName() + ": tx3 " + group + " " + user);
        //TODO: Change this
//        group.ref().addUser(user);

        return 2;
    }
}
