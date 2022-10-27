package de.tuda.stg.consys.demo.twitterclone;

import de.tuda.stg.consys.bench.BenchmarkConfig;
import de.tuda.stg.consys.bench.BenchmarkOperations;
import de.tuda.stg.consys.bench.BenchmarkUtils;
import de.tuda.stg.consys.demo.DemoRunnable;
import de.tuda.stg.consys.demo.DemoUtils;
import de.tuda.stg.consys.demo.JBenchExecution;
import de.tuda.stg.consys.demo.JBenchStore;
import de.tuda.stg.consys.demo.twitterclone.schema.ITweet;
import de.tuda.stg.consys.demo.twitterclone.schema.IUser;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.TransactionContext;
import de.tuda.stg.consys.logging.Logger;
import scala.Function1;
import scala.Option;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeoutException;


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

    private final int nMaxRetries;
    private final int retryDelay;

    private final int numOfGroupsPerReplica;
    private final Class<? extends IUser> userImpl;
    private final Class<? extends ITweet> tweetImpl;

    private final List<Ref<? extends IUser>> users;
    private final List<Ref<? extends ITweet>> tweets;

    public TwitterCloneBenchmark(JBenchStore adapter, BenchmarkConfig config) {
        super(adapter, config);

        numOfGroupsPerReplica = config.toConfig().getInt("consys.bench.demo.twitterclone.users");

        nMaxRetries = config.toConfig().getInt("consys.bench.demo.twitterclone.retries");
        retryDelay = config.toConfig().getInt("consys.bench.demo.twitterclone.retryDelay");

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

    @Override
    public void setup() {
        System.out.println("Adding users and tweets");
        for (int grpIndex = 0; grpIndex <= numOfGroupsPerReplica; grpIndex++) {
            int finalGrpIndex = grpIndex;

            Ref<? extends IUser> user;
            Ref<? extends ITweet> tweet;

            if (benchType == BenchmarkType.MIXED) {
                user = (Ref<? extends IUser>) store().transaction(ctx -> Option.apply(ctx.replicate(
                        DemoUtils.addr("user", finalGrpIndex, processId()), getLevelWithMixedFallback(getWeakLevel()), userImpl,
                        DemoUtils.generateRandomName()))).get();
                var retweetCount = store().transaction(ctx -> Option.apply(ctx.replicate(
                        DemoUtils.addr("retweetCount", finalGrpIndex, processId()), getLevelWithMixedFallback(getStrongLevel()),
                        de.tuda.stg.consys.demo.twitterclone.schema.datacentric.Counter.class,
                        0))).get();
                tweet = (Ref<? extends ITweet>) store().transaction(ctx -> Option.apply(ctx.replicate(
                        DemoUtils.addr("tweet", finalGrpIndex, processId()), getLevelWithMixedFallback(getWeakLevel()), tweetImpl,
                        user, DemoUtils.generateRandomText(3), retweetCount))).get();
            } else {
                user = (Ref<? extends IUser>) store().transaction(ctx -> Option.apply(ctx.replicate(
                        DemoUtils.addr("user", finalGrpIndex, processId()), getLevelWithMixedFallback(getWeakLevel()), userImpl,
                        DemoUtils.generateRandomName()))).get();
                tweet = (Ref<? extends ITweet>) store().transaction(ctx -> Option.apply(ctx.replicate(
                        DemoUtils.addr("tweet", finalGrpIndex, processId()), getLevelWithMixedFallback(getWeakLevel()), tweetImpl,
                        user, DemoUtils.generateRandomText(3)))).get();
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
                        DemoUtils.addr("user", finalGrpIndex, finalReplIndex), getLevelWithMixedFallback(getWeakLevel()), userImpl))).get();

                Ref<? extends ITweet> tweet = (Ref<? extends ITweet>) store().transaction(ctx -> Option.apply(ctx.lookup(
                        DemoUtils.addr("tweet", finalGrpIndex, finalReplIndex), getLevelWithMixedFallback(getWeakLevel()), tweetImpl))).get();

                users.add(user);
                tweets.add(tweet);
            }
        }
        BenchmarkUtils.printDone();
    }

    @Override
    public void cleanup() {
        users.clear();
        tweets.clear();
    }

    @Override
    public void test() {
        if (processId() == 0) printTestResult();
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

    private <U> Option<U> withRetry(Function1<TransactionContext, Option<U>> code) {
        int nTries = 0;
        while (true) {
            try {
                return store().transaction(code::apply);
            } catch (Exception e) {
                if (!(e instanceof TimeoutException)) throw e;
                Logger.warn("Timeout during operation. Retrying...");
                nTries++;
                try { Thread.sleep(random.nextInt(retryDelay)); } catch (InterruptedException ignored) {}
                if (nTries > nMaxRetries) {
                    Logger.err("Timeout during operation. Max retries reached.");
                    throw e;
                }
            }
        }
    }

    private void follow() {
        Ref<? extends IUser> follower = DemoUtils.getRandomElement(users);
        Ref<? extends IUser> following = DemoUtils.getRandomElementExcept(users, follower);

        store().transaction(ctx -> {
            follower.ref().addFollower(following);
            following.ref().addFollowing(follower);

            return Option.apply(0);
        });
    }

    private void unfollow() {
        Ref<? extends IUser> follower = DemoUtils.getRandomElement(users);
        Ref<? extends IUser> following = DemoUtils.getRandomElement(users);

        store().transaction(ctx -> {
            follower.ref().removeFollower(following);
            following.ref().removeFollowing(follower);

            return Option.apply(0);
        });
    }

    private void retweet() {
        Ref<? extends ITweet> tweet = DemoUtils.getRandomElement(tweets);
        Ref<? extends IUser> user = DemoUtils.getRandomElement(users);

        Option<Integer> prevRetweetsResults = withRetry(ctx -> {
            int prevRetweets = isTestMode ? tweet.ref().getRetweets() : -1;

            tweet.ref().retweet();
            user.ref().addRetweet(tweet);

            return Option.apply(prevRetweets);
        });

        if (isTestMode) {
            store().transaction(ctx -> {
                check("retweet was incremented", prevRetweetsResults.get() < tweet.ref().getRetweets());
                return Option.apply(0);
            });
        }
    }

    private void readTimeline() {
        Ref<? extends IUser> user = DemoUtils.getRandomElement(users);

        store().transaction(ctx -> {
            List<Ref<? extends ITweet>> timeline = user.ref().getTimeline();

            return Option.apply(0);
        });
    }
}
