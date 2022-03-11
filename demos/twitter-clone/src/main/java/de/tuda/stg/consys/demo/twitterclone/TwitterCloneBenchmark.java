package de.tuda.stg.consys.demo.twitterclone;

import com.typesafe.config.Config;
import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.bench.OutputFileResolver;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.demo.CassandraDemoBenchmark;
import de.tuda.stg.consys.bench.BenchmarkUtils;
import de.tuda.stg.consys.demo.twitterclone.schema.Counter;
import de.tuda.stg.consys.demo.twitterclone.schema.Tweet;
import de.tuda.stg.consys.demo.twitterclone.schema.User;
import de.tuda.stg.consys.japi.Ref;
import org.checkerframework.com.google.common.collect.Sets;
import scala.Option;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;


/**
 * Created on 10.10.19.
 *
 * @author Mirko Köhler
 */
public class TwitterCloneBenchmark extends CassandraDemoBenchmark {

    public static void main(String[] args) {
        start(TwitterCloneBenchmark.class, args);
    }

    private final int numOfGroupsPerReplica;

    private static final List<String> WORDS = new ArrayList<>(Arrays.asList("small batch", "Etsy", "axe", "plaid", "McSweeney's", "VHS",
            "viral", "cliche", "post-ironic", "health", "goth", "literally", "Austin",
            "brunch", "authentic", "hella", "street art", "Tumblr", "Blue Bottle", "readymade",
            "occupy", "irony", "slow-carb", "heirloom", "YOLO", "tofu", "ethical", "tattooed",
            "vinyl", "artisan", "kale", "selfie"));
    private static final List<String> FIRST_NAMES = new ArrayList<>(Arrays.asList("Arthur", "Ford", "Tricia", "Zaphod"));
    private static final List<String> LAST_NAMES = new ArrayList<>(Arrays.asList("Dent", "Prefect", "McMillan", "Beeblebrox"));

    private final List<Ref<User>> users;
    private final List<Ref<Tweet>> tweets;

    private final Random random = new Random();

    public TwitterCloneBenchmark(Config config, Option<OutputFileResolver> outputResolver) {
        super(config, outputResolver);

        numOfGroupsPerReplica = config.getInt("consys.bench.demo.twitterclone.users");

        tweets = new ArrayList<>(numOfGroupsPerReplica * nReplicas());
        users = new ArrayList<>(numOfGroupsPerReplica * nReplicas());
    }

    private static String addr(String identifier, int grpIndex, int replIndex) {
        return identifier + "$" + grpIndex + "$"+ replIndex;
    }

    private String generateRandomName() {
        return FIRST_NAMES.get(random.nextInt(FIRST_NAMES.size()))
                + " " + LAST_NAMES.get(random.nextInt(LAST_NAMES.size()));
    }

    private String generateRandomText(int n) {
        String body = WORDS.get(random.nextInt(WORDS.size()));
        for (int i = 0; i < n - 1; i++)
            body += " " + WORDS.get(random.nextInt(WORDS.size()));
        return body;
    }

    private Ref<User> randomUser() {
        return users.get(random.nextInt(users.size()));
    }

    @Override
    public void setup() {
        System.out.println("Adding users");
        for (int grpIndex = 0; grpIndex <= numOfGroupsPerReplica; grpIndex++) {
            int finalGrpIndex = grpIndex;

            Ref<@Weak User> user = store().transaction(ctx -> Option.apply(ctx.replicate(
                    addr("user", finalGrpIndex, processId()), getWeakLevel(), User.class, generateRandomName()))).get();
            Ref<@Weak Counter> retweetCount = store().transaction(ctx -> Option.apply(ctx.replicate(
                    addr("retweetCount", finalGrpIndex, processId()), getStrongLevel(), Counter.class, 0))).get();
            Ref<@Weak Tweet> tweet = store().transaction(ctx -> Option.apply(ctx.replicate(
                    addr("tweet", finalGrpIndex, processId()), getWeakLevel(), Tweet.class, user, generateRandomText(3), retweetCount))).get();

            store().transaction(ctx -> {
                user.ref().addToTimeline(tweet);
                return Option.empty();
            });

            BenchmarkUtils.printProgress(grpIndex);
        }

        barrier("twitter_setup");

        for (int grpIndex = 0; grpIndex <= numOfGroupsPerReplica; grpIndex++) {
            for (int replIndex = 0; replIndex < nReplicas(); replIndex++) {
                int finalGrpIndex = grpIndex;
                int finalReplIndex = replIndex;

                Ref<@Weak User> user = store().transaction(ctx -> Option.apply(ctx.lookup(
                        addr("user", finalGrpIndex, finalReplIndex), getWeakLevel(), User.class))).get();

                Ref<@Weak Tweet> tweet = store().transaction(ctx -> Option.apply(ctx.lookup(
                        addr("tweet", finalGrpIndex, finalReplIndex), getWeakLevel(), Tweet.class))).get();

                users.add(user);
                tweets.add(tweet);
            }
        }
        BenchmarkUtils.printDone();
    }

    @Override
    public void cleanup() {
        super.cleanup();
        //system().clear(Sets.newHashSet());
        users.clear();
        tweets.clear();

        try {
            Thread.sleep(1000);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }
    }

    @Override
    public void operation() {
        store().transaction(ctx -> {
            randomTransaction();
            return Option.empty();
        });
    }

    @Transactional
    private int randomTransaction() {
        int rand = random.nextInt(100);
        if (rand < 12) /*12*/ {
            // follow
            return transaction1();
        } else if (rand < 58) {
            // unfollow
            return transaction2();
        } else if (rand < 80) {
            // retweet
            return transaction3();
        } else if (rand < 100) {
            // read timeline
            return transaction4();
        }

        throw new IllegalStateException("cannot be here");
    }

    @Transactional
    private int transaction1() {
        Ref<User> follower = randomUser();
        Ref<User> following = randomUser();

        follower.ref().addFollower(following);
        following.ref().addFollowing(follower);

        return 0;
    }

    @Transactional
    private int transaction2() {
        Ref<User> follower = randomUser();
        Ref<User> following = randomUser();

        follower.ref().removeFollower(following);
        following.ref().removeFollowing(follower);

        return 1;
    }

    @Transactional
    private int transaction3() {
        Ref<Tweet> tweet = tweets.get(random.nextInt(tweets.size()));
        Ref<User> user = randomUser();

        tweet.ref().retweet();
        user.ref().addRetweet(tweet);

        return 2;
    }

    @Transactional
    private int transaction4() {
        Ref<User> user = randomUser();

        List<Ref<Tweet>> timeline = user.ref().getTimeline();

        return 3;
    }
}
