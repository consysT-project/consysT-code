package de.tuda.stg.consys.triggerchat;

import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.core.store.cassandra.CassandraStore;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;
import de.tuda.stg.consys.triggerchat.schema.opcentric.Group;
import de.tuda.stg.consys.triggerchat.schema.opcentric.Inbox;
import de.tuda.stg.consys.triggerchat.schema.opcentric.User;
import scala.Function1;
import scala.Option;

import java.util.Random;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

import static de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.MIXED;

@SuppressWarnings({"consistency"})
public class Session {
    private CassandraStoreBinding store;
    private Ref<Group> group;
    private Ref<Inbox> inbox;
    private Ref<User> user;
    public static ConsistencyLevel<CassandraStore> groupConsistencyLevel = MIXED;
    public static ConsistencyLevel<CassandraStore> inboxConsistencyLevel = MIXED;
    public static ConsistencyLevel<CassandraStore> userConsistencyLevel = MIXED;
    private static ExecutorService threadPool;

    private <U> Option<U> doTransaction(Function1<CassandraTransactionContextBinding, Option<U>> code) {
        return store.transaction(code::apply);
    }

    public Session(@Mutable CassandraStoreBinding store) {
        this.store = store;
        threadPool = Executors.newFixedThreadPool(1);
    }

    public void init() {
        this.group = doTransaction(
                ctx -> Option.apply(ctx.replicate("group", groupConsistencyLevel, Group.class))).get();

        this.inbox = doTransaction(
                ctx -> Option.apply(ctx.replicate("inbox", inboxConsistencyLevel, Inbox.class))).get();

        this.user = doTransaction(
                ctx -> Option.apply(ctx.replicate("user", userConsistencyLevel, User.class, "Jan", inbox))).get();
    }

    public void sendMessage(String message) {
        doTransaction(ctx -> {
            user.ref().send(message);
            return Option.apply(true);
        });
    }

    public void runSimulation() {
        threadPool.submit(new Simulation());
    }

    public void stopSimulation() {
        threadPool.shutdown();
    }

    class Simulation implements Runnable {
        @Override
        public void run() {
            while (true) {

                String[] names = {"Alice", "Bob", "Charlie", "David", "Emily", "Frank", "Grace", "Henry", "Isabella", "John"};
                int index = new Random().nextInt(names.length);
                String randomName = names[index];

                Ref<Inbox> inbox = doTransaction(
                        ctx -> Option.apply(ctx.replicate("inbox_" + randomName, inboxConsistencyLevel, Inbox.class))).get();

                Ref<User> user = doTransaction(
                        ctx -> Option.apply(ctx.replicate(randomName, userConsistencyLevel, User.class, randomName, inbox))).get();

                String[] messages = {"Hello!", "How are you?", "Nice to meet you.", "Have a good day!", "See you later!", "Thank you!", "You're welcome!", "Good luck!", "Congratulations!", "Happy birthday!"};
                int index2 = new Random().nextInt(messages.length);
                String randomMessage = messages[index2];

                doTransaction(ctx -> {
                    group.ref().addUser(user);
                    String msg = randomName + ": " + randomMessage;
                    group.ref().postMessage(msg);
                    return Option.apply(true);
                });

                try {
                    Thread.sleep(8000);
                } catch (InterruptedException e) {
                    throw new RuntimeException(e);
                }

            }
        }
    }

}
