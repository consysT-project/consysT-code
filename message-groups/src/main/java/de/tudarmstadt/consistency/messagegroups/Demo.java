package de.tudarmstadt.consistency.messagegroups;

import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.replobj.japi.JConsistencyLevel;
import de.tudarmstadt.consistency.replobj.japi.JRef;
import de.tudarmstadt.consistency.replobj.japi.JReplicaSystem;

import java.util.*;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

import static de.tudarmstadt.consistency.messagegroups.Replicas.replicaSystems;


public class Demo {

	public static void main(String... args) throws Exception {
        runBenchmark();
    }

    public static void runBenchmark() throws InterruptedException {

        int numReplicas = replicaSystems.length;

         System.out.println("Initializing benchmarks...");
        MessageGroupsBenchmark[] benchmarks = MessageGroupsBenchmark.createWith(replicaSystems, 10000);

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
                    JRef<Group> group = replicaSystems[j].replicate("group$" + i + "$"+ j, new Group(), JConsistencyLevel.STRONG);
                    JRef<Inbox> inbox =  replicaSystems[j].replicate("inbox$" + i + "$" + j, new Inbox(), JConsistencyLevel.WEAK);
                    JRef<User> user = replicaSystems[j].replicate("user$" + i + "$"+ j, new User(inbox, "alice$" + i + "$"+ j), JConsistencyLevel.WEAK);

                    Thread.sleep(2);
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
                    JRef<Group> group = replicaSystem.ref("group$" + i + "$" + j, Group.class, JConsistencyLevel.STRONG);
                    JRef<User> user = replicaSystem.ref("user$" + i + "$" + j, User.class, JConsistencyLevel.WEAK);

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




//    public static void main(String... args) throws Exception {
//        JRef<@Strong ConcertHall> concertHall = replicaSystem1.replicate(new ConcertHall(5), JConsistencyLevel.STRONG);
//        JRef<@Weak Band> band = replicaSystem1.replicate(new Band("some band"), JConsistencyLevel.WEAK);
//        JRef<@Strong Counter> soldTickets = replicaSystem1.replicate(new Counter(0), JConsistencyLevel.STRONG);
//        JRef<@Strong ConcertMixed> concert1 = replicaSystem1.replicate("concert", new ConcertMixed(new Date(), concertHall, band, soldTickets), JConsistencyLevel.STRONG);
//
//        JRef<@Strong ConcertMixed> concert2 = replicaSystem2.ref("concert", ConcertMixed.class, JConsistencyLevel.STRONG);
//
//        Thread.sleep(1000);
//
//        System.out.println(
//                "concert1: " + concert1.<JRef<@Strong Counter>>getField("soldTickets").<Integer>getField("value") + " " +
//                "concert2: " + concert2.<JRef<@Strong Counter>>getField("soldTickets").<Integer>getField("value"));
//        System.out.println(
//                "band1: \"" + concert1.<JRef<@Weak Band>>getField("band").<String>getField("name") + "\" " +
//                "band2: \"" + concert2.<JRef<@Weak Band>>getField("band").<String>getField("name") + "\"");
//
//        System.out.println("-> change band name");
//        concert1.<JRef<@Weak Band>>getField("band").setField("name", "some other band");
//
//        System.out.println("-> buy ticket");
//        concert1.invoke("buyTicket");
//
//        System.out.println(
//                "concert1: " + concert1.<JRef<@Strong Counter>>getField("soldTickets").<Integer>getField("value") + " " +
//                "concert2: " + concert2.<JRef<@Strong Counter>>getField("soldTickets").<Integer>getField("value"));
//        System.out.println(
//                "band1: \"" + concert1.<JRef<@Weak Band>>getField("band").<String>getField("name") + "\" " +
//                "band2: \"" + concert2.<JRef<@Weak Band>>getField("band").<String>getField("name") + "\"");
//
//
//        System.out.println("-> manual synchronization");
//
//
//        // manually access "soldTickets"
//
//        ReplicatedObject<@Strong ConcertWeak> replica1 = ReplicatedObject.from(concert2);
//
//        AkkaReplicaSystem.GlobalContext$ context1 = replica1.internal.replicaSystem().context();
//
//        boolean needNewTx = !context1.hasBuilder();
//
//        if (needNewTx) context1.startNewTransaction();
//
//        ContextPath path = context1.getBuilder().nextPath(ConsistencyLevel.Weak$.MODULE$);
//
//        context1.getBuilder().push(ConsistencyLevel.Weak$.MODULE$);
//
//        Requests.RequestHandler<String> handler1 =
//                replica1.internal.replicaSystem().acquireHandlerFrom(
//                        replica1.master,
//                        replica1.internal.replicaSystem().acquireHandlerFrom$default$2());
//        StrongAkkaReplicaSystem.ReadResult readResult =
//                (StrongAkkaReplicaSystem.ReadResult) handler1.request(
//                        replica1.address,
//                        new StrongAkkaReplicaSystem.ReadStrongField(new Requests.GetFieldOp<>(path, "soldTickets")),
//                        handler1.request$default$3());
//        JRef<@Weak Counter> result1 = (JRef<@Weak Counter>) readResult.res();
//        handler1.close();
//
//        replica1.system.initializeRefFieldsFor(result1);
//
//        context1.getBuilder().pop();
//
//        if (needNewTx) context1.endTransaction();
//
//
//        // manually access "value" of "soldTickets"
//
//        ReplicatedObject<@Strong Counter> replica2 = ReplicatedObject.from(result1);
//
//        AkkaReplicaSystem.GlobalContext$ context2 = replica2.internal.replicaSystem().context();
//
//        context2.startNewTransaction();
//
//        Requests.RequestHandler<String> handler2 =
//                replica2.internal.replicaSystem().acquireHandlerFrom(
//                        replica2.master,
//                        replica2.internal.replicaSystem().acquireHandlerFrom$default$2());
//        WeakAkkaReplicaSystem.WeakSynchronized weakSynchronized =
//                (WeakAkkaReplicaSystem.WeakSynchronized) handler2.request(
//                        replica2.address,
//                        new WeakAkkaReplicaSystem.SynchronizeWithWeakMaster(replica2.localOperations),
//                        handler2.request$default$3());
//        Counter result2 = (Counter) weakSynchronized.obj();
//        handler2.close();
//
//        replica2.internal.setObject(result2);
//        replica2.localOperations.clear();
//
//        context2.endTransaction();
//
//
//        System.out.println(
//                "concert1: " + concert1.<JRef<@Strong Counter>>getField("soldTickets").<Integer>getField("value") + " " +
//                "concert2: " + result2.value);
//    }
}
