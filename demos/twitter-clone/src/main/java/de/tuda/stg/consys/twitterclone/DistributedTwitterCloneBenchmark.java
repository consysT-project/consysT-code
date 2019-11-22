package de.tuda.stg.consys.twitterclone;

import com.typesafe.config.Config;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.demo.DemoBenchmark;
import de.tuda.stg.consys.demo.DemoUtils;
import de.tuda.stg.consys.objects.japi.JConsistencyLevels;
import de.tuda.stg.consys.twitterclone.schema.Tweet;
import de.tuda.stg.consys.twitterclone.schema.User;
import de.tuda.stg.consys.twitterclone.schema.Counter;
import de.tuda.stg.consys.objects.japi.JRef;
import org.checkerframework.com.google.common.collect.Sets;

import java.util.*;

/**
 * Created on 10.10.19.
 *
 * @author Mirko Köhler
 */
public class DistributedTwitterCloneBenchmark extends DemoBenchmark {


    public static void main(String[] args) {
        start(DistributedTwitterCloneBenchmark.class, args[0]);
    }

    private final int numOfGroupsPerReplica;
    private final int numOfTransactions;

    private static final List<String> WORDS = new ArrayList<>(Arrays.asList("small batch", "Etsy", "axe", "plaid", "McSweeney's", "VHS",
            "viral", "cliche", "post-ironic", "health", "goth", "literally", "Austin",
            "brunch", "authentic", "hella", "street art", "Tumblr", "Blue Bottle", "readymade",
            "occupy", "irony", "slow-carb", "heirloom", "YOLO", "tofu", "ethical", "tattooed",
            "vinyl", "artisan", "kale", "selfie"));
    private static final List<String> FIRST_NAMES = new ArrayList<>(Arrays.asList("Arthur", "Ford", "Tricia", "Zaphod"));
    private static final List<String> LAST_NAMES = new ArrayList<>(Arrays.asList("Dent", "Prefect", "McMillan", "Beeblebrox"));

    private final List<JRef<User>> users;
    private final List<JRef<Tweet>> tweets;

    private final Random random = new Random();

    public DistributedTwitterCloneBenchmark(Config config) {
        super(config);

        numOfGroupsPerReplica = config.getInt("consys.bench.demo.twitterclone.users");
        numOfTransactions = config.getInt("consys.bench.demo.twitterclone.transactions");

        tweets = new ArrayList<>(numOfGroupsPerReplica * numOfReplicas());
        users = new ArrayList<>(numOfGroupsPerReplica * numOfReplicas());
    }

    private static String addr(String identifier, int grpIndex, int replIndex) {
        return identifier + "$" + grpIndex + "$"+ replIndex;
    }


    private int numOfReplicas() {
        return replicaSystem().numOfReplicas();
    }

    private String generateRandomName() {
        String name = FIRST_NAMES.get(random.nextInt(FIRST_NAMES.size()))
                + " " + LAST_NAMES.get(random.nextInt(LAST_NAMES.size()));
        return name;
    }

    private String generateRandomText(int n) {
        String body = WORDS.get(random.nextInt(WORDS.size()));
        for (int i = 0; i < n - 1; i++)
            body += " " + WORDS.get(random.nextInt(WORDS.size()));
        return body;
    }

    private JRef<User> randomUser() {
        return users.get(random.nextInt(users.size()));
    }

    @Override
    public void setup() {
        System.out.println("Adding users");
        for (int grpIndex = 0; grpIndex <= numOfGroupsPerReplica; grpIndex++) {

            JRef<@Weak User> user = replicaSystem().replicate
                    (addr("user", grpIndex, processId()), new User(generateRandomName()), getWeakLevel());
            JRef<@Strong Counter> retweetCount =  replicaSystem().replicate(
                    addr("retweetCount", grpIndex, processId()), new Counter(0), getStrongLevel());
            JRef<@Weak Tweet> tweet = replicaSystem().replicate(
                    addr("tweet", grpIndex, processId()), new Tweet(user, generateRandomText(3), retweetCount), getWeakLevel());

            user.ref().addToTimeline(tweet);

            DemoUtils.printProgress(grpIndex);
        }

        for (int grpIndex = 0; grpIndex <= numOfGroupsPerReplica; grpIndex++) {
            for (int replIndex = 0; replIndex < numOfReplicas(); replIndex++) {
                JRef<@Weak User> user = replicaSystem().lookup(
                        addr("user", grpIndex, replIndex), User.class, getWeakLevel());
                JRef<@Weak Tweet> tweet = replicaSystem().lookup(
                        addr("tweet", grpIndex, replIndex), Tweet.class, getWeakLevel());

                users.add(user);
                tweets.add(tweet);
            }
        }
        DemoUtils.printDone();
    }

    @Override
    public void iteration() {
        for (int i = 0; i < numOfTransactions; i++) {
            randomTransaction();
            DemoUtils.printProgress(i);
        }
        DemoUtils.printDone();
    }

    @Override
    public void cleanup() {
        replicaSystem().clear(Sets.newHashSet());
    }


    private int transaction1() {
        JRef<User> follower = randomUser();
        JRef<User> following = randomUser();

        follower.ref().addFollower(following);
        following.ref().addFollowing(follower);

        if (random.nextInt(100) < 20) {
            follower.sync();
            following.sync();
        }

        return 0;
    }

    private int transaction2() {
        JRef<User> follower = randomUser();
        JRef<User> following = randomUser();

        follower.ref().removeFollower(following);
        following.ref().removeFollowing(follower);

        if (random.nextInt(100) < 20) {
            follower.sync();
            following.sync();
        }

        return 1;
    }

    private int transaction3() {
        JRef<Tweet> tweet = tweets.get(random.nextInt(tweets.size()));
        JRef<User> user = randomUser();

        tweet.ref().retweet();
        user.ref().addRetweet(tweet);

        if (random.nextInt(100) < 20) {
            tweet.sync();
            user.sync();
        }

        return 2;
    }

    private int transaction4() {
        JRef<User> user = randomUser();

        List<JRef<Tweet>> timeline = user.ref().getTimeline();

        if (random.nextInt(100) < 20) user.sync();

        return 3;
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
            return transaction4();
        }

        throw new IllegalStateException("cannot be here");
    }


}
