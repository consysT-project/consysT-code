package de.tuda.stg.consys.demo.twitterclone;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.demo.twitterclone.schema.Counter;
import de.tuda.stg.consys.demo.twitterclone.schema.Tweet;
import de.tuda.stg.consys.demo.twitterclone.schema.User;
import de.tuda.stg.consys.japi.legacy.JConsistencyLevels;
import de.tuda.stg.consys.japi.legacy.JRef;
import de.tuda.stg.consys.japi.legacy.JReplicaSystem;
import de.tuda.stg.consys.japi.legacy.impl.JReplicaSystems;
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
    private static final List<String> WORDS = new ArrayList<>(Arrays.asList("small batch", "Etsy", "axe", "plaid", "McSweeney's", "VHS",
            "viral", "cliche", "post-ironic", "health", "goth", "literally", "Austin",
            "brunch", "authentic", "hella", "street art", "Tumblr", "Blue Bottle", "readymade",
            "occupy", "irony", "slow-carb", "heirloom", "YOLO", "tofu", "ethical", "tattooed",
            "vinyl", "artisan", "kale", "selfie"));
    private static final List<String> FIRST_NAMES = new ArrayList<>(Arrays.asList("Arthur", "Ford", "Tricia", "Zaphod"));
    private static final List<String> LAST_NAMES = new ArrayList<>(Arrays.asList("Dent", "Prefect", "McMillan", "Beeblebrox"));
    /*####################################################*/



    public static void main(String[] args) throws Exception {

        Main.main(args);

    }




    @State(Scope.Thread)
    public static class BenchmarkSetup {

        private static final int GRPS_PER_REPL = NUM_OF_GROUPS / NUM_OF_REPLICAS;
        private final Random random = new Random();

        //initialized by setup
        JReplicaSystem[] replicaSystems = new JReplicaSystem[NUM_OF_REPLICAS];
        BMessageGroupsBenchmark[] benchmarks;


        @Setup(Level.Iteration)
        public void setup() throws InterruptedException {

            /* Initialize replicas */
            System.out.println("Initialize replicas...");
            replicaSystems = JReplicaSystems.fromActorSystemForTesting(NUM_OF_REPLICAS);

            System.out.println("Adding users");
            for (int grpIndex = 0; grpIndex <= NUM_OF_GROUPS / NUM_OF_REPLICAS; grpIndex++) {
                for (int replIndex = 0; replIndex < NUM_OF_REPLICAS; replIndex++) {

                    JRef<@Weak User> user = replicaSystems[replIndex].replicate
                            (addr("user", grpIndex, replIndex), new User(generateRandomName()), JConsistencyLevels.WEAK);
                    JRef<@Strong Counter> retweetCount =  replicaSystems[replIndex].replicate(
                            addr("retweetCount", grpIndex,replIndex), new Counter(0), JConsistencyLevels.STRONG);
                    JRef<@Weak Tweet> tweet = replicaSystems[replIndex].replicate(
                            addr("tweet", grpIndex, replIndex), new Tweet(user, generateRandomText(3), retweetCount), JConsistencyLevels.WEAK);

                    user.ref().addToTimeline(tweet);
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

        public String generateRandomName() {
            String name = FIRST_NAMES.get(random.nextInt(FIRST_NAMES.size()))
                    + " " + LAST_NAMES.get(random.nextInt(LAST_NAMES.size()));
            return name;
        }

        public String generateRandomText(int n) {
            String body = WORDS.get(random.nextInt(WORDS.size()));
            for (int i = 0; i < n - 1; i++)
                body += " " + WORDS.get(random.nextInt(WORDS.size()));
            return body;
        }

        private static String addr(String identifier, int grpIndex, int replIndex) {
            return identifier + "$" + grpIndex + "$"+ replIndex;
        }


        static class BMessageGroupsBenchmark {

            private final List<JRef<@Weak User>> users = new ArrayList<>(NUM_OF_GROUPS);
            private final List<JRef<@Weak Tweet>> tweets = new ArrayList<>(NUM_OF_GROUPS);

            private final Random random = new Random();

            private final JReplicaSystem replicaSystem;

            BMessageGroupsBenchmark(JReplicaSystem replicaSystem) {
                this.replicaSystem = replicaSystem;
            }

            public JRef<User> randomUser() {
                return users.get(random.nextInt(users.size()));
            }


            private void initialize() {

                for (int grpIndex = 0; grpIndex <= NUM_OF_GROUPS; grpIndex++) {
                    for (int replIndex = 0; replIndex < NUM_OF_REPLICAS; replIndex++) {
                        JRef<@Weak User> user = replicaSystem.lookup(addr("user", grpIndex, replIndex), User.class, JConsistencyLevels.WEAK);
                        JRef<@Weak Tweet> tweet = replicaSystem.lookup(addr("tweet", grpIndex, replIndex), Tweet.class, JConsistencyLevels.WEAK);

                        users.add(user);
                        tweets.add(tweet);

                    }
                }
            }

            private int transaction1() {
                JRef<User> follower = randomUser();
                JRef<User> following = randomUser();

                follower.ref().addFollower(following);
                following.ref().addFollowing(follower);

                return 0;
            }

            private int transaction2() {
                JRef<User> follower = randomUser();
                JRef<User> following = randomUser();

                follower.ref().removeFollower(following);
                following.ref().removeFollowing(follower);

                return 1;
            }

            private int transaction3() {
                JRef<Tweet> tweet = tweets.get(random.nextInt(tweets.size()));
                JRef<User> user = randomUser();

                tweet.ref().retweet();
                user.ref().addRetweet(tweet);

                return 2;
            }


            private int randomTransaction() {
                int rand = random.nextInt(100);
                if (rand < 12) /*12*/ {
                    //Follow
                    return transaction1();
                } else if (rand < 58) {
                    //Unfollow
                    return transaction2();
                } else if (rand < 80) {
                    //Retweet
                    return transaction3();
                } else if (rand < 100) {
                    return 3;//transaction3();
                }

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
            for(int replIndex = 0; replIndex < NUM_OF_REPLICAS; replIndex++) {
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

