package de.tuda.stg.consys.demo.triggerchat;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.bench.BenchmarkUtils;
import de.tuda.stg.consys.demo.DemoRunnable;
import de.tuda.stg.consys.demo.DemoUtils;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import de.tuda.stg.consys.logging.Logger;
import de.tuda.stg.consys.demo.triggerchat.schema.datecentric.Group;
import de.tuda.stg.consys.demo.triggerchat.schema.datecentric.Inbox;
import de.tuda.stg.consys.demo.triggerchat.schema.datecentric.User;
import scala.Option;

import java.util.ArrayList;
import java.util.List;

@SuppressWarnings({"consistency"})
public class TriggerChatBenchmark extends DemoRunnable {
    public static void main(String[] args) {
        JBenchExecution.execute("trigger-chat", TriggerChatBenchmark.class, args);
    }

    private int numOfUsersPerReplica;
    private int numOfGroupsPerReplica;
    private final List<Session> localSessions;
    private final List<Ref<? extends User>> users;
    private final List<Ref<? extends Group>> groups;
    private final List<Ref<? extends Inbox>> inboxes;


    public TriggerChatBenchmark(JBenchStore adapter, BenchmarkConfig config) {
        super(adapter, config);

        localSessions = new ArrayList<>();

        users = new ArrayList<>();
        groups = new ArrayList<>();
        inboxes = new ArrayList<>();

        numOfGroupsPerReplica = config.toConfig().getInt("consys.bench.demo.trigger-chat.groups");
        numOfUsersPerReplica = config.toConfig().getInt("consys.bench.demo.trigger-chat.users");

        Session.groupConsistencyLevel = getLevelWithMixedFallback(getStrongLevel());
        Session.inboxConsistencyLevel = getLevelWithMixedFallback(getStrongLevel());
        Session.userConsistencyLevel = getLevelWithMixedFallback(getStrongLevel());
    }

    @Override
    public void setup() {
        Logger.debug(procName(), "Creating objects");

        for (int userIndex = 0; userIndex < numOfUsersPerReplica; userIndex++) {
            var session = new Session((CassandraStoreBinding) store());
            localSessions.add(session);

            session.initInbox(DemoUtils.addr("inbox", userIndex, processId()));

            session.initUser(DemoUtils.addr("user", userIndex, processId()), DemoUtils.generateRandomName());

            for (int groupIndex = 0; groupIndex < numOfGroupsPerReplica; groupIndex++) {
                session.initGroup(DemoUtils.addr("group" + groupIndex, userIndex, processId()));
            }

            BenchmarkUtils.printProgress(userIndex);
        }

        barrier("users_added");

        Logger.debug(procName(), "Collecting objects");

        for (int userIndex = 0; userIndex < numOfUsersPerReplica; userIndex++) {
            for (int replicaIndex = 0; replicaIndex < nReplicas; replicaIndex++) {
                users.add(localSessions.get(0).findUser(DemoUtils.addr("user", userIndex, replicaIndex)));


                for (int groupIndex = 0; groupIndex < numOfGroupsPerReplica; groupIndex++) {
                    groups.add(localSessions.get(0).findGroup(DemoUtils.addr("group" + groupIndex, userIndex, replicaIndex)));
                }
            }
        }
        BenchmarkUtils.printDone();
    }

    @Override
    public void cleanup() {
        localSessions.clear();
        users.clear();
        groups.clear();
        inboxes.clear();
    }

    @Override
    public BenchmarkOperations operations() {
        return BenchmarkOperations.withZipfDistribution(new Runnable[] {
                this::joinGroup,
                this::sendMessage,
        });
    }

    private void joinGroup() {
        Ref<? extends Group> group = DemoUtils.getRandomElement(groups);
        Ref<? extends Group> group2 = DemoUtils.getRandomElement(groups);
        Ref<? extends Group> group3 = DemoUtils.getRandomElement(groups);
        Ref<? extends Group> group4 = DemoUtils.getRandomElement(groups);
        Ref<? extends Group> group5 = DemoUtils.getRandomElement(groups);
        Ref<User> user = (Ref<User>) DemoUtils.getRandomElement(users);

        store().transaction(ctx -> {
            group.ref().addUser(user);
            group2.ref().addUser(user);
            group3.ref().addUser(user);
            group4.ref().addUser(user);
            group5.ref().addUser(user);
            return Option.apply(0);
        });
    }

    private void sendMessage() {
        Ref<? extends User> user = DemoUtils.getRandomElement(users);

        store().transaction(ctx -> {
            user.ref().send(DemoUtils.generateRandomText(3));
            user.ref().send(DemoUtils.generateRandomText(3));
            user.ref().send(DemoUtils.generateRandomText(3));
            user.ref().send(DemoUtils.generateRandomText(3));
            user.ref().send(DemoUtils.generateRandomText(3));
            return Option.apply(0);
        });
    }

}
