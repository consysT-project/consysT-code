package de.tuda.stg.consys.demo.messagegroups;

import com.typesafe.config.Config;
import de.tuda.stg.consys.bench.OutputFileResolver;
import de.tuda.stg.consys.demo.DemoBenchmark;
import de.tuda.stg.consys.bench.BenchmarkUtils;
import de.tuda.stg.consys.demo.messagegroups.schema.Group;
import de.tuda.stg.consys.demo.messagegroups.schema.Inbox;
import de.tuda.stg.consys.demo.messagegroups.schema.User;
import de.tuda.stg.consys.japi.legacy.JRef;
import org.checkerframework.com.google.common.collect.Sets;
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
public class MessageGroupsBenchmark extends DemoBenchmark {
    public static void main(String[] args) {
        start(MessageGroupsBenchmark.class, args);
    }

    private final int numOfGroupsPerReplica;
    private final int numOfWeakGroupsPerReplica;

    private final List<JRef<Group>> groups;
    private final List<JRef<User>> users;

    private final Random random = new Random();

    public MessageGroupsBenchmark(Config config, Option<OutputFileResolver> outputResolver) {
        super(config, outputResolver);

        numOfGroupsPerReplica = config.getInt("consys.bench.demo.messagegroups.groups");
        numOfWeakGroupsPerReplica = config.getInt("consys.bench.demo.messagegroups.weakGroups");

        groups = new ArrayList<>(numOfGroupsPerReplica * numOfReplicas());
        users = new ArrayList<>(numOfGroupsPerReplica * numOfReplicas());
    }

    private static String addr(String identifier, int grpIndex, int replIndex) {
        return identifier + "$" + grpIndex + "$" + replIndex;
    }


    private int numOfReplicas() {
        return replicas().length; //TODO: Change to system().numOfReplicas();
    }

    @Override
    public void setup() {
        System.out.println("Adding users");
        for (int grpIndex = 0; grpIndex <= numOfGroupsPerReplica; grpIndex++) {
            try {
                if (grpIndex < numOfWeakGroupsPerReplica) {
                    system().replicate(
                            addr("group", grpIndex, processId()), new Group(), getWeakLevel());
                } else {
                    system().replicate(
                            addr("group", grpIndex, processId()), new Group(), getStrongLevel());
                }
                Thread.sleep(33);


                JRef<Inbox> inbox = system().replicate(
                        addr("inbox", grpIndex, processId()), new Inbox(), getWeakLevel());
                Thread.sleep(33);

                system().replicate(
                        addr("user", grpIndex, processId()), new User(inbox, addr("alice", grpIndex, processId())), getWeakLevel());
                Thread.sleep(33);

                BenchmarkUtils.printProgress(grpIndex);
            } catch (InterruptedException e) {
                e.printStackTrace();
            }
        }
        BenchmarkUtils.printDone();

        system().barrier("users_added");

        for (int grpIndex = 0; grpIndex <= numOfGroupsPerReplica; grpIndex++) {
            for (int replIndex = 0; replIndex < numOfReplicas(); replIndex++) {
                JRef<Group> group;

                if (grpIndex < numOfWeakGroupsPerReplica) {
                    group = system().lookup(
                            addr("group", grpIndex, replIndex), Group.class, getWeakLevel());
                } else {
                    group = system().lookup(
                            addr("group", grpIndex, replIndex), Group.class, getStrongLevel());
                }

                JRef<User> user = system().lookup(
                        addr("user", grpIndex, replIndex), User.class, getWeakLevel());

                if (replIndex == processId()) {
                    group.ref().addUser(user);
                    group.sync();
                }

                groups.add(group);
                users.add(user);
            }
            BenchmarkUtils.printProgress(grpIndex);
        }
        BenchmarkUtils.printDone();
    }


    @Override
    public void operation() {
        randomTransaction();
        System.out.print(".");
    }



    @Override
    public void cleanup() {
        system().clear(Sets.newHashSet());
        try {
            Thread.sleep(1000);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }


    private int transaction1() {
        int i = random.nextInt(groups.size());
        JRef<Group> group = groups.get(i);
        //   System.out.println(Thread.currentThread().getName() +  ": tx1 " + group);
        group.ref().addPost("Hello " + i);
        return 2;
    }

    private int transaction1b() {
        int i = random.nextInt(groups.size());
        JRef<Group> group = groups.get(i);
        //   System.out.println(Thread.currentThread().getName() +  ": tx1 " + group);
        group.ref().addPost("Hello " + i);
        doSync(() -> group.sync());
        return 2;
    }

    private int transaction2() {
        int i = random.nextInt(users.size());
        JRef<User> user = users.get(i);
        // System.out.println(Thread.currentThread().getName() + ": tx2 " + user);

        //No sync
        Set<String> inbox = user.ref().getInbox();
        return 1;
    }

    private int transaction2b() {
        int i = random.nextInt(users.size());
        JRef<User> user = users.get(i);
        // System.out.println(Thread.currentThread().getName() + ": tx2b " + user);

        JRef<Inbox> inbox = user.ref().inbox;
        doSync(() -> {
            user.sync();
            inbox.sync();
        });
        Set<String> inboxVal = user.ref().getInbox();

        return 0;
    }


    private int transaction3() {
        int i = random.nextInt(groups.size());
        int j = random.nextInt(users.size());

        JRef<Group> group = groups.get(i);
        JRef<User> user = users.get(j);

        //  System.out.println(Thread.currentThread().getName() + ": tx3 " + group + " " + user);
        group.ref().addUser(user);
        doSync(() -> group.sync());

        return 3;
    }

    private int counter = 0;
    private boolean shouldSync = false;
    private int randomTransaction2() {
        counter++;
        int rand = counter % 10;
        if (rand < 5) /*12*/ {
            //inbox checking with sync
            return transaction2b();
        } else if (rand < 6) /*12*/ {
            //inbox checking with sync
            shouldSync = true;
            int res = transaction2b();
            shouldSync = false;
            return res;
        } else if (rand < 7) {
            //Message posting
            return transaction1b();
        }  else if (rand < 8) {
            //Message posting
            shouldSync = true;
            int res = transaction1b();
            shouldSync = false;
            return res;
        } else if (rand < 9) {
            //group joining
            return transaction3();
        } else if (rand < 10) {
            //group joining
            shouldSync = true;
            int res = transaction3();
            shouldSync = false;
            return res;
        }

        //user creation: left out
        throw new IllegalStateException("cannot be here");
    }

    private int randomTransaction() {
        int rand = random.nextInt(100);
        if (rand < 58) /*12*/ {
            //inbox checking with sync
            return transaction2b(); //use 2b for syncing here
        } else if (rand < 80) {
            //Message posting
            return transaction1b();
        } else if (rand < 100) {
            //group joining
            return transaction3();
        }
        //user creation: left out

        throw new IllegalStateException("cannot be here");
    }

    @Override
    protected boolean shouldSync() {
        return shouldSync;
    }


}
