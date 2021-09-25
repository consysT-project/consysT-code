package bench;

import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.Cassandra;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import scala.Option;
import scala.concurrent.duration.Duration;

import java.util.Random;

import static de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.*;

public class TwitterDemo {
    static final int nTweets = 100;
    static final long msTimeout = 100;
    static final long msRetry = 50;

    public static abstract class TwitterBench implements Bench {
        protected final Random random = new Random();

        public void operation() {
            int roll = random.nextInt(100);
            if (roll < 12) {
                unfollowTransaction();
            } else if (roll < 28) {
                followTransaction();
            } else if (roll < 52) {
                retweetTransaction();
            } else {
                viewTimelineTransaction();
            }
        }

        protected abstract void unfollowTransaction();
        protected abstract void followTransaction();
        protected abstract void retweetTransaction();
        protected abstract void viewTimelineTransaction();
    }

    public static class Mixed extends TwitterBench {
        private CassandraStoreBinding store;
        private final Ref<demos.twitter.consystop.Tweet>[] tweets = new Ref[nTweets];
        private final Ref<demos.twitter.consystop.User>[] users = new Ref[nTweets];

        public void setup(int id) {
            if (id == 0) {
                store = Cassandra.newReplica("127.0.0.1", 9042, 2181, Duration.apply(msTimeout, "ms"), true);
                for (int i = 0; i < nTweets; i++) {
                    int finalI = i;
                    store.transaction(ctx -> {
                        users[finalI] = ctx.replicate("user" + finalI, WEAK, demos.twitter.consystop.User.class, "user" + finalI);
                        tweets[finalI] = ctx.replicate("tweet" + finalI, MIXED, demos.twitter.consystop.Tweet.class, users[finalI], "body");
                        users[finalI].ref().addToTimeline(tweets[finalI]);
                        return Option.empty();
                    });
                }
            } else {
                store = Cassandra.newReplica("127.0.0." + (id+1), 9042, 2181, Duration.apply(msTimeout, "ms"), false);
                for (int i = 0; i < nTweets; i++) {
                    int finalI = i;
                    store.transaction(ctx -> {
                        users[finalI] = ctx.lookup("user" + finalI, WEAK, demos.twitter.consystop.User.class);
                        tweets[finalI] = ctx.lookup("group" + finalI, MIXED, demos.twitter.consystop.Tweet.class);
                        return Option.empty();
                    });
                }
            }
        }

        public void shutdown() {
            try {
                store.close();
            } catch (Exception ignored) {}
        }

        protected void followTransaction() {
            int u1 = random.nextInt(users.length);
            int u2 = random.nextInt(users.length);
            doTransaction(() -> {
                store.transaction(ctx -> {
                    users[u1].ref().addFollower(users[u2]);
                    users[u2].ref().addFollowing(users[u1]);
                    return Option.empty();
                });
                return null;
            }, msRetry);
        }

        protected void unfollowTransaction() {
            int u1 = random.nextInt(users.length);
            int u2 = random.nextInt(users.length);
            doTransaction(() -> {
                store.transaction(ctx -> {
                    users[u1].ref().removeFollower(users[u2]);
                    users[u2].ref().removeFollowing(users[u1]);
                    return Option.empty();
                });
                return null;
            }, msRetry);
        }

        protected void retweetTransaction() {
            int u = random.nextInt(users.length);
            int t = random.nextInt(tweets.length);
            doTransaction(() -> {
                store.transaction(ctx -> {
                    users[u].ref().addRetweet(tweets[t]);
                    return Option.empty();
                });
                return null;
            }, msRetry);
        }

        protected void viewTimelineTransaction() {
            int u = random.nextInt(users.length);
            doTransaction(() -> {
                store.transaction(ctx -> {
                    users[u].ref().getTimeline();
                    return Option.empty();
                });
                return null;
            }, msRetry);
        }
    }

    public static class Mono extends TwitterBench {
        private CassandraStoreBinding store;
        private final Ref<demos.twitter.consyst.Tweet>[] tweets = new Ref[nTweets];
        private final Ref<demos.twitter.consyst.User>[] users = new Ref[nTweets];

        public void setup(int id) {
            if (id == 0) {
                store = Cassandra.newReplica("127.0.0.1", 9042, 2181, Duration.apply(msTimeout, "ms"), true);
                for (int i = 0; i < nTweets; i++) {
                    int finalI = i;
                    store.transaction(ctx -> {
                        users[finalI] = ctx.replicate("user" + finalI, WEAK, demos.twitter.consyst.User.class, "user" + finalI);
                        var counter = ctx.replicate("counter" + finalI, STRONG, demos.twitter.consyst.Counter.class, 0);
                        tweets[finalI] = ctx.replicate("tweet" + finalI, WEAK, demos.twitter.consyst.Tweet.class, users[finalI], "body", counter);
                        users[finalI].ref().addToTimeline(tweets[finalI]);
                        return Option.empty();
                    });
                }
            } else {
                store = Cassandra.newReplica("127.0.0." + (id+1), 9042, 2181, Duration.apply(msTimeout, "ms"), false);
                for (int i = 0; i < nTweets; i++) {
                    int finalI = i;
                    store.transaction(ctx -> {
                        users[finalI] = ctx.lookup("user" + finalI, WEAK, demos.twitter.consyst.User.class);
                        tweets[finalI] = ctx.lookup("group" + finalI, WEAK, demos.twitter.consyst.Tweet.class);
                        return Option.empty();
                    });
                }
            }
        }

        public void shutdown() {
            try {
                store.close();
            } catch (Exception ignored) {}
        }

        protected void followTransaction() {
            int u1 = random.nextInt(users.length);
            int u2 = random.nextInt(users.length);
            doTransaction(() -> {
                store.transaction(ctx -> {
                    users[u1].ref().addFollower(users[u2]);
                    users[u2].ref().addFollowing(users[u1]);
                    return Option.empty();
                });
                return null;
            }, msRetry);
        }

        protected void unfollowTransaction() {
            int u1 = random.nextInt(users.length);
            int u2 = random.nextInt(users.length);
            doTransaction(() -> {
                store.transaction(ctx -> {
                    users[u1].ref().removeFollower(users[u2]);
                    users[u2].ref().removeFollowing(users[u1]);
                    return Option.empty();
                });
                return null;
            }, msRetry);
        }

        protected void retweetTransaction() {
            int u = random.nextInt(users.length);
            int t = random.nextInt(tweets.length);
            doTransaction(() -> {
                store.transaction(ctx -> {
                    users[u].ref().addRetweet(tweets[t]);
                    return Option.empty();
                });
                return null;
            }, msRetry);
        }

        protected void viewTimelineTransaction() {
            int u = random.nextInt(users.length);
            doTransaction(() -> {
                store.transaction(ctx -> {
                    users[u].ref().getTimeline();
                    return Option.empty();
                });
                return null;
            }, msRetry);
        }
    }
}
