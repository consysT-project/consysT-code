package de.tuda.stg.consys.demo.twitterclone;

import com.typesafe.config.Config;
import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.bench.BenchmarkUtils;
import de.tuda.stg.consys.bench.OutputResolver;
import de.tuda.stg.consys.core.store.ConsistencyLevel;
import de.tuda.stg.consys.demo.CassandraDemoBenchmark;
import de.tuda.stg.consys.demo.DemoRunnable;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.twitterclone.schema.ITweet;
import de.tuda.stg.consys.demo.twitterclone.schema.IUser;
import de.tuda.stg.consys.japi.Ref;
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
@SuppressWarnings({"consistency"})
public class TwitterCloneBenchmark extends DemoRunnable {

    public static void main(String[] args) {
        JBenchExecution.execute("twitter-clone", TwitterCloneBenchmark.class, args);
    }

    private final int numOfGroupsPerReplica;
    private final Class<? extends IUser> userImpl;
    private final Class<? extends ITweet> tweetImpl;

    private static final List<String> WORDS = new ArrayList<>(Arrays.asList("small batch", "Etsy", "axe", "plaid", "McSweeney's", "VHS",
            "viral", "cliche", "post-ironic", "health", "goth", "literally", "Austin",
            "brunch", "authentic", "hella", "street art", "Tumblr", "Blue Bottle", "readymade",
            "occupy", "irony", "slow-carb", "heirloom", "YOLO", "tofu", "ethical", "tattooed",
            "vinyl", "artisan", "kale", "selfie"));
    private static final List<String> FIRST_NAMES = new ArrayList<>(Arrays.asList("Arthur", "Ford", "Tricia", "Zaphod"));
    private static final List<String> LAST_NAMES = new ArrayList<>(Arrays.asList("Dent", "Prefect", "McMillan", "Beeblebrox"));

    private final List<Ref<? extends IUser>> users;
    private final List<Ref<? extends ITweet>> tweets;

    private final Random random = new Random();

    public TwitterCloneBenchmark(JBenchStore adapter, BenchmarkConfig config) {
        super(adapter, config);

        numOfGroupsPerReplica = config.toConfig().getInt("consys.bench.demo.twitterclone.users");

        if (benchType == BenchmarkType.MIXED) {
            userImpl = de.tuda.stg.consys.demo.twitterclone.schema.datacentric.User.class;
            tweetImpl = de.tuda.stg.consys.demo.twitterclone.schema.datacentric.Tweet.class;
        } else {
            userImpl = de.tuda.stg.consys.demo.twitterclone.schema.opcentric.User.class;
            tweetImpl = de.tuda.stg.consys.demo.twitterclone.schema.opcentric.Tweet.class;
        }

        tweets = new ArrayList<>(numOfGroupsPerReplica * nReplicas);
        users = new ArrayList<>(numOfGroupsPerReplica * nReplicas);
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

    @Override
    public void setup() {
        System.out.println("Adding users and tweets");
        for (int grpIndex = 0; grpIndex <= numOfGroupsPerReplica; grpIndex++) {
            int finalGrpIndex = grpIndex;

            Ref<? extends IUser> user;
            Ref<? extends ITweet> tweet;

            if (benchType == BenchmarkType.MIXED) {
                user = (Ref<? extends IUser>) store().transaction(ctx -> Option.apply(ctx.replicate(
                        addr("user", finalGrpIndex, processId()), getLevel(userImpl), userImpl,
                        generateRandomName()))).get();
                var retweetCount = store().transaction(ctx -> Option.apply(ctx.replicate(
                        addr("retweetCount", finalGrpIndex, processId()), getLevel(de.tuda.stg.consys.demo.twitterclone.schema.datacentric.Counter.class),
                        de.tuda.stg.consys.demo.twitterclone.schema.datacentric.Counter.class,
                        0))).get();
                tweet = (Ref<? extends ITweet>) store().transaction(ctx -> Option.apply(ctx.replicate(
                        addr("tweet", finalGrpIndex, processId()), getLevel(tweetImpl), tweetImpl,
                        user, generateRandomText(3), retweetCount))).get();
            } else {
                user = (Ref<? extends IUser>) store().transaction(ctx -> Option.apply(ctx.replicate(
                        addr("user", finalGrpIndex, processId()), getLevel(userImpl), userImpl,
                        generateRandomName()))).get();
                tweet = (Ref<? extends ITweet>) store().transaction(ctx -> Option.apply(ctx.replicate(
                        addr("tweet", finalGrpIndex, processId()), getLevel(tweetImpl), tweetImpl,
                        user, generateRandomText(3)))).get();
            }

            store().transaction(ctx -> {
                user.ref().addToTimeline(tweet);
                return Option.apply(0);
            });

            BenchmarkUtils.printProgress(grpIndex);
        }

        barrier("twitter_setup");

        System.out.println("Collecting remote objects");
        for (int grpIndex = 0; grpIndex <= numOfGroupsPerReplica; grpIndex++) {
            for (int replIndex = 0; replIndex < nReplicas; replIndex++) {
                int finalGrpIndex = grpIndex;
                int finalReplIndex = replIndex;

                Ref<? extends IUser> user = (Ref<? extends IUser>) store().transaction(ctx -> Option.apply(ctx.lookup(
                            addr("user", finalGrpIndex, finalReplIndex), getLevel(userImpl), userImpl))).get();

                Ref<? extends ITweet> tweet = (Ref<? extends ITweet>) store().transaction(ctx -> Option.apply(ctx.lookup(
                            addr("tweet", finalGrpIndex, finalReplIndex), getLevel(tweetImpl), tweetImpl))).get();

                users.add(user);
                tweets.add(tweet);
            }
        }
        BenchmarkUtils.printDone();
    }

    private <T> ConsistencyLevel getLevel(Class<T> clazz) {
        switch (benchType) {
            case WEAK: return getWeakLevel();
            case STRONG: return getStrongLevel();
            case OP_MIXED: return getMixedLevel();
            case MIXED:
                if (clazz == de.tuda.stg.consys.demo.twitterclone.schema.datacentric.Counter.class)
                    return getStrongLevel();
                else
                    return getWeakLevel();
            default: throw new UnsupportedOperationException("unknown bench type");
        }
    }

    @Override
    public void cleanup() {
        users.clear();
        tweets.clear();
    }

    @Override
    public BenchmarkOperations operations() {
        return BenchmarkOperations.withZipfDistribution(new Runnable[] {
                this::readTimeline,
                this::retweet,
                this::follow,
                this::unfollow
        });
    }

    private void follow() {
        Ref<? extends IUser> follower = getRandomElement(users);
        Ref<? extends IUser> following = getRandomElementExcept(users, follower);

        store().transaction(ctx -> {
            follower.ref().addFollower(following);
            following.ref().addFollowing(follower);

            return Option.apply(0);
        });
    }

    private void unfollow() {
        Ref<? extends IUser> follower = getRandomElement(users);
        Ref<? extends IUser> following = getRandomElement(users);

        store().transaction(ctx -> {
            follower.ref().removeFollower(following);
            following.ref().removeFollowing(follower);

            return Option.apply(0);
        });
    }

    private void retweet() {
        Ref<? extends ITweet> tweet = getRandomElement(tweets);
        Ref<? extends IUser> user = getRandomElement(users);

        Option<Integer> result = store().transaction(ctx -> {
            int prevRetweets = isTestMode ? tweet.ref().getRetweets() : -1;

            tweet.ref().retweet();
            user.ref().addRetweet(tweet);

            return Option.apply(prevRetweets);
        });

        if (isTestMode) {
            store().transaction(ctx -> {
                check("retweet was incremented", result.get().equals(tweet.ref().getRetweets() - 1));
                return Option.apply(0);
            });
        }
    }

    private void readTimeline() {
        Ref<? extends IUser> user = getRandomElement(users);

        store().transaction(ctx -> {
            List<Ref<? extends ITweet>> timeline = user.ref().getTimeline();

            return Option.apply(0);
        });
    }
}
