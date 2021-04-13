package de.tuda.stg.consys.demo.messagegroups;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.demo.messagegroups.schema.Group;
import de.tuda.stg.consys.demo.messagegroups.schema.Inbox;
import de.tuda.stg.consys.demo.messagegroups.schema.User;
import de.tuda.stg.consys.japi.legacy.JConsistencyLevels;
import de.tuda.stg.consys.japi.legacy.JRef;
import de.tuda.stg.consys.japi.legacy.JReplicaSystem;
import org.openjdk.jmh.Main;
import org.openjdk.jmh.annotations.*;

import java.util.*;
import java.util.concurrent.TimeUnit;

/**
 * Created on 08.04.19.
 *
 * @author Mirko Köhler
 */
//Note: Currently not working. Use Demo.java instead.
@BenchmarkMode(Mode.Throughput)
@OutputTimeUnit(TimeUnit.MICROSECONDS)
public class JMHBenchmark {


    /*####################################################*/
    /* Change these to change the general benchmark setup */
    static final int NUM_OF_REPLICAS = 4;
    static final int NUM_OF_GROUPS = 40000;
    /*####################################################*/


    public static void main(String[] args) throws Exception {
//		Options opt = new OptionsBuilder()
//			.include(MessageGroupsBenchmark.class.getSimpleName())
//			.threads(4).forks(1).build();
//
//		new Runner(opt).run();

        Main.main(args);

    }


    @State(Scope.Thread)
    public static class BenchmarkSetup {

        private static final int GRPS_PER_REPL = NUM_OF_GROUPS / NUM_OF_REPLICAS;


        //initialized by setup
        JReplicaSystem[] replicaSystems = new JReplicaSystem[NUM_OF_REPLICAS];
        BMessageGroupsBenchmark[] benchmarks;


        @Setup(Level.Iteration)
        public void setup() throws InterruptedException {

            /* Initialize replicas */
            System.out.println("Initialize replicas...");
//			JReplicaSystems.fromActorSystemForTesting(NUM_OF_REPLICAS);

            /* Add users */
            System.out.println("Adding users");
            for (int grpIndex = 0; grpIndex <= NUM_OF_GROUPS / NUM_OF_REPLICAS; grpIndex++) {
                for (int replIndex = 0; replIndex < NUM_OF_REPLICAS; replIndex++) {

                    JRef<Group> group = replicaSystems[replIndex].replicate
                            (name("group", grpIndex, replIndex), new Group(), JConsistencyLevels.STRONG);
                    JRef<Inbox> inbox = replicaSystems[replIndex].replicate(
                            name("inbox", grpIndex, replIndex), new Inbox(), JConsistencyLevels.WEAK);
                    JRef<User> user = replicaSystems[replIndex].replicate(
                            name("user", grpIndex, replIndex), new User(inbox, name("alice", grpIndex, replIndex)), JConsistencyLevels.WEAK);

                    group.invoke("addUser", user);
                }
                System.out.print(grpIndex % 100 == 0 ? grpIndex : ".");
            }
            System.out.println("done");


            Thread.sleep(1000);


            BMessageGroupsBenchmark[] benchmarks = new BMessageGroupsBenchmark[4];
            //Initialize benchmarks
            for (int i = 0; i < NUM_OF_REPLICAS; i++) {
                benchmarks[i] = new BMessageGroupsBenchmark(replicaSystems[i]);
                benchmarks[i].initialize();
            }
        }


        private static String name(String identifier, int grpIndex, int replIndex) {
            return identifier + "$" + grpIndex + "$" + replIndex;
        }


        static class BMessageGroupsBenchmark {

            private final List<JRef<@Strong Group>> groups = new ArrayList<>(NUM_OF_GROUPS);
            private final List<JRef<@Weak User>> users = new ArrayList<>(NUM_OF_GROUPS);

            private Random random = new Random();

            private final JReplicaSystem replicaSystem;

            BMessageGroupsBenchmark(JReplicaSystem replicaSystem) {
                this.replicaSystem = replicaSystem;
            }


            private void initialize() {

                for (int grpIndex = 0; grpIndex <= NUM_OF_GROUPS; grpIndex++) {
                    for (int replIndex = 0; replIndex < NUM_OF_REPLICAS; replIndex++) {
                        JRef<Group> group = replicaSystem.lookup(
                                name("group", grpIndex, replIndex), Group.class, JConsistencyLevels.STRONG);
                        JRef<User> user = replicaSystem.lookup(
                                name("user", grpIndex, replIndex), User.class, JConsistencyLevels.WEAK);

                        groups.add(group);
                        users.add(user);
                    }
                }
            }

            private int transaction1() {
                int i = random.nextInt(groups.size());
                JRef<Group> group = groups.get(i);
                //   System.out.println(Thread.currentThread().getName() +  ": tx1 " + group);
                group.invoke("addPost", "Hello " + i);
                return 2;
            }

            private int transaction2() {
                int i = random.nextInt(users.size());
                JRef<User> user = users.get(i);
                // System.out.println(Thread.currentThread().getName() + ": tx2 " + user);

                //No sync
                Set<String> inbox = user.invoke("getInbox");
                return 1;
            }

            private int transaction2b() {
                int i = random.nextInt(users.size());
                JRef<User> user = users.get(i);
                // System.out.println(Thread.currentThread().getName() + ": tx2b " + user);

                JRef<Inbox> inbox = user.getField("inbox");
                user.sync();
                inbox.sync();
                Set<String> inboxVal = user.invoke("getInbox");

                return 0;
            }


            private int transaction3() {
                int i = random.nextInt(groups.size());
                int j = random.nextInt(users.size());

                JRef<Group> group = groups.get(i);
                JRef<User> user = users.get(j);

                //  System.out.println(Thread.currentThread().getName() + ": tx3 " + group + " " + user);
                group.invoke("addUser", user);

                return 3;
            }


            private int randomTransaction() {
                int rand = random.nextInt(100);
                if (rand < 58) /*12*/ {
                    //inbox checking with sync
                    return transaction2b();
                } else if (rand < 58) {
                    return transaction2();
                } else if (rand < 80) {
                    //Message posting
                    return transaction1();
                } else if (rand < 100) {
                    //group joining
                    return transaction3();
                }
                //user creation: left out

                throw new IllegalStateException("cannot be here");
            }

            int[] count = null;

            public void runFor(int milliseconds) {

                long start = System.currentTimeMillis();

                count = new int[4];

                System.out.println("Starting run at " + new Date(start));

                while (System.currentTimeMillis() < start + milliseconds) {
                    int i = randomTransaction();
                    count[i]++;
                }

                System.out.println("Ending run at " + new Date());

                System.out.println("Total number of transactions: " + Arrays.toString(count));

            }

        }


        @TearDown(Level.Iteration)
        public void teardown() throws Exception {
            for (int replIndex = 0; replIndex < NUM_OF_REPLICAS; replIndex++) {
                replicaSystems[replIndex].close();
            }
        }
    }


    @Benchmark
    @Fork(NUM_OF_REPLICAS)
    @Warmup(iterations = 5, time = 180)
    @Measurement(iterations = 5, time = 180)
    public void benchmark(BenchmarkSetup setup) {
        System.out.println("benchmark");
    }


}

