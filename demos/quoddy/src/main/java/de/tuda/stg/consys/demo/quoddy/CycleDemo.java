package de.tuda.stg.consys.demo.quoddy;

import de.tuda.stg.consys.demo.quoddy.schema.IUser;
import de.tuda.stg.consys.demo.quoddy.schema.opcentric.StatusUpdate;
import de.tuda.stg.consys.demo.quoddy.schema.opcentric.User;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraReplica;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import scala.Option;
import scala.concurrent.duration.Duration;

import java.util.*;
import java.util.concurrent.Callable;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeoutException;
import java.util.function.Function;

import static de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.STRONG;

@SuppressWarnings({"consistency"})
public class CycleDemo {
    private static CassandraStoreBinding r0;
    private static CassandraStoreBinding r1;
    private static CassandraStoreBinding r2;
    private static final int nRuns = 2;
    private static final int msReplicaTimeout = 5000;

    public static void main(String[] args) throws Exception {
        r0 = CassandraReplica.create("127.0.0.1", 9042, 2181, "datacenter1",
                Duration.apply(msReplicaTimeout, "ms"), true);
        r1 = CassandraReplica.create("127.0.0.2", 9042, 2182, "datacenter1",
                Duration.apply(msReplicaTimeout, "ms"), false);
        r2 = CassandraReplica.create("127.0.0.3", 9042, 2183, "datacenter1",
                Duration.apply(msReplicaTimeout, "ms"), false);

        Boolean[] results = new Boolean[nRuns];
        for (int i = 0; i < nRuns; i++) {
            results[i] = test();
        }

        long nSuccesses = Arrays.stream(results).filter(r -> r).count();
        System.out.println(nSuccesses + "/" + nRuns + " runs succeeded");

        r0.close();
        r1.close();
        r2.close();
    }

    private static boolean test() throws Exception {
        System.out.println("run start");

        var pool = Executors.newFixedThreadPool(2);
        var tasks = new ArrayList<Callable<Boolean>>(2);

        // setup
        var user0 = r0.transaction(ctx -> Option.apply(ctx.replicate("u0", STRONG, User.class, "u0", "u0"))).get();
        var user1 = r0.transaction(ctx -> Option.apply(ctx.replicate("u1", STRONG, User.class, "u1", "u1"))).get();
        r0.transaction(ctx -> {
            user0.ref().addFriend(user1);
            user1.ref().addFriend(user0);
            return Option.apply(0);
        });

        tasks.add(() -> {
            System.out.println("  " + new Date().toInstant() + " | start T1");
            boolean success = addPost(r1, user0);
            System.out.println("  " + new Date().toInstant() + " | end T1");
            return success;
        });

        tasks.add(() -> {
            System.out.println("  " + new Date().toInstant() + " | start T2");
            boolean success = addPost(r2, user1);
            System.out.println("  " + new Date().toInstant() + " | end T2");
            return success;
        });

        List<Boolean> results = new LinkedList<>();
        for (var f : pool.invokeAll(tasks)) {
            results.add(f.get());
        }
        pool.shutdown();

        sleep(100);
        // test result
        System.out.println("  " + new Date().toInstant());

        System.out.println("run end");
        return results.stream().allMatch(r -> r);
    }

    private static boolean addPost(CassandraStoreBinding r, Ref<User> user) {
        try {
            r.transaction(ctx -> {
                var id = UUID.randomUUID();
                var status = ctx.replicate(id.toString(), STRONG, StatusUpdate.class, id, user, "");

                user.ref().addPost(status);
                // cyclic dependency for all-strong case: if two friends post simultaneously, they end up waiting for each
                // other's locks here
                sleep(1000);
                for (Ref<? extends IUser> friend : user.ref().getFriends()) {
                    System.out.println(user.ref().getName() + " | " + friend.ref().getName());
                    friend.ref().addPost(status);
                }

                return Option.apply(0);
            });
            return true;
        } catch (Exception e) {
            if (e instanceof TimeoutException){
                System.out.println(e.getMessage());
                return false;
            }
            else throw e;
        }
    }

    private static void sleep(int msTime) {
        try { Thread.sleep(msTime); } catch (InterruptedException e) { e.printStackTrace(); }
    }
}
