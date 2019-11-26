package de.tuda.stg.consys.demo.twitterclone;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.demo.twitterclone.schema.Counter;
import de.tuda.stg.consys.demo.twitterclone.schema.Replicas;
import de.tuda.stg.consys.demo.twitterclone.schema.Tweet;
import de.tuda.stg.consys.demo.twitterclone.schema.User;
import de.tuda.stg.consys.japi.JConsistencyLevels;
import de.tuda.stg.consys.japi.JRef;
import de.tuda.stg.consys.japi.JReplicaSystem;

import java.util.*;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

public class Demo {
    public static void main(String[] args) throws Exception{
        runBenchmark();
    }

    public static void runBenchmark() throws InterruptedException {
        int numReplicas = Replicas.replicaSystems.length;

        System.out.println("Initializing benchmarks...");
        MessageGroupsBenchmark[] benchmarks = MessageGroupsBenchmark.createWith(Replicas.replicaSystems, 10);

        //Run benchmarks
        System.out.println("Run benchmarks...");
        ExecutorService exec = Executors.newFixedThreadPool(numReplicas);
        for (int i = 0; i < numReplicas; i++) {
            final int index = i;
            exec.submit(() -> benchmarks[index].runFor(1000));
        }
    }

    static class MessageGroupsBenchmark {
        private static final List<String> WORDS = new ArrayList<>(Arrays.asList("small batch", "Etsy", "axe", "plaid", "McSweeney's", "VHS",
                "viral", "cliche", "post-ironic", "health", "goth", "literally", "Austin",
                "brunch", "authentic", "hella", "street art", "Tumblr", "Blue Bottle", "readymade",
                "occupy", "irony", "slow-carb", "heirloom", "YOLO", "tofu", "ethical", "tattooed",
                "vinyl", "artisan", "kale", "selfie"));
        private static final List<String> FIRST_NAMES = new ArrayList<>(Arrays.asList("Arthur", "Ford", "Tricia", "Zaphod"));
        private static final List<String> LAST_NAMES = new ArrayList<>(Arrays.asList("Dent", "Prefect", "McMillan", "Beeblebrox"));

        private final List<JRef<@Weak User>> users = new ArrayList<>(400);
        private final List<JRef<@Weak Tweet>> tweets = new ArrayList<>(400);

        private static Random random = new Random();

        private final JReplicaSystem replicaSystem;

        public static String generateRandomName() {
            String name = FIRST_NAMES.get(random.nextInt(FIRST_NAMES.size()))
                    + " " + LAST_NAMES.get(random.nextInt(LAST_NAMES.size()));
            return name;
        }

        public static String generateRandomText(int n) {
            String body = WORDS.get(random.nextInt(WORDS.size()));
            for (int i = 0; i < n - 1; i++)
                body += " " + WORDS.get(random.nextInt(WORDS.size()));
            return body;
        }

        public JRef<User> randomUser() {
            return users.get(random.nextInt(users.size()));
        }

        MessageGroupsBenchmark(JReplicaSystem replicaSystem) {
            this.replicaSystem = replicaSystem;
        }

        public static MessageGroupsBenchmark[] createWith(JReplicaSystem[] replicaSystems, int entriesPerSystem) throws InterruptedException {

            for (int i = 0; i <= entriesPerSystem; i++) {
                for (int j = 0; j < replicaSystems.length; j++) {
                    JRef<@Weak User> user = replicaSystems[j].replicate("user$" + i + "$"+ j, new User(generateRandomName()), JConsistencyLevels.WEAK);
                    JRef<@Strong Counter> retweetCount = replicaSystems[j].replicate("counter" + i + "$"+ j, new Counter(0), JConsistencyLevels.STRONG);
                    JRef<@Weak Tweet> tweet = replicaSystems[j].replicate("tweet$" + i + "$"+ j, new Tweet(user, generateRandomText(3), retweetCount), JConsistencyLevels.WEAK);

                    user.ref().addToTimeline(tweet);
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
                    JRef<@Weak User> user = replicaSystem.lookup("user$" + i + "$" + j, User.class, JConsistencyLevels.WEAK);
                    JRef<@Weak Tweet> tweet = replicaSystem.lookup("tweet$" + i + "$" + j, Tweet.class, JConsistencyLevels.WEAK);

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
                //group joining
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
}
