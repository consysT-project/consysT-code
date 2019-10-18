package de.tuda.stg.consys.demo.messagegroups;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.demo.messagegroups.schema.Group;
import de.tuda.stg.consys.demo.messagegroups.schema.Inbox;
import de.tuda.stg.consys.demo.messagegroups.schema.Replicas;
import de.tuda.stg.consys.demo.messagegroups.schema.User;
import de.tuda.stg.consys.objects.japi.JConsistencyLevels;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;

import java.util.*;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;


public class Demo {

	public static void main(String... args) throws Exception {
        runBenchmark();
    }

    public static void runBenchmark() throws InterruptedException {

        int numReplicas = Replicas.replicaSystems.length;

         System.out.println("Initializing benchmarks...");
        MessageGroupsBenchmark[] benchmarks = MessageGroupsBenchmark.createWith(Replicas.replicaSystems, 10000);

        //Run benchmarks
        System.out.println("Run benchmarks...");
        ExecutorService exec = Executors.newFixedThreadPool(numReplicas);
        for (int i = 0; i < numReplicas; i++) {
            final int index = i;
            exec.submit(() -> benchmarks[index].runFor(180000));
        }
    }


    static class MessageGroupsBenchmark {

        private final List<JRef<@Strong Group>> groups = new ArrayList<>(40000);
        private final List<JRef<@Weak User>> users = new ArrayList<>(40000);

        private Random random = new Random();

        private final JReplicaSystem replicaSystem;

        MessageGroupsBenchmark(JReplicaSystem replicaSystem) {
            this.replicaSystem = replicaSystem;
        }

        public static MessageGroupsBenchmark[] createWith(JReplicaSystem[] replicaSystems, int entriesPerSystem) throws InterruptedException {

            for (int i = 0; i <= entriesPerSystem; i++) {

                for (int j = 0; j < replicaSystems.length; j++) {
                    JRef<Group> group = replicaSystems[j].replicate("group$" + i + "$"+ j, new Group(), JConsistencyLevels.STRONG);
                    JRef<Inbox> inbox =  replicaSystems[j].replicate("inbox$" + i + "$" + j, new Inbox(), JConsistencyLevels.WEAK);
                    JRef<User> user = replicaSystems[j].replicate("user$" + i + "$"+ j, new User(inbox, "alice$" + i + "$"+ j), JConsistencyLevels.WEAK);

                    group.invoke("addUser", user);
                    System.out.println("Added user$" + i + "$"+ j);
                }
            }

            Thread.sleep(1000);


            MessageGroupsBenchmark[] benchmarks = new MessageGroupsBenchmark[4];
            //Initialize benchmarks
            for (int i = 0; i < 4; i++) {
                benchmarks[i] = new MessageGroupsBenchmark(replicaSystems[i]);
                benchmarks[i].initialize(entriesPerSystem, replicaSystems.length);
            }

            return benchmarks;
        }

        private void initialize(int entriesPerSystem, int numReplicas) {

            for (int i = 0; i <= entriesPerSystem; i++) {
                for (int j = 0; j < numReplicas; j++) {
                    JRef<Group> group = replicaSystem.lookup("group$" + i + "$" + j, Group.class, JConsistencyLevels.STRONG);
                    JRef<User> user = replicaSystem.lookup("user$" + i + "$" + j, User.class, JConsistencyLevels.WEAK);

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


}
