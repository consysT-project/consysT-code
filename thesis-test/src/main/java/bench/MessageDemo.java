package bench;

import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.Cassandra;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import scala.Option;
import scala.concurrent.duration.Duration;

import static de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.*;

import java.util.Random;

public class MessageDemo {
    static final int nGroups = 10;
    static final int nUsers = 100;
    static long msTimeout = 100;
    static long msRetry = 50;

    public static abstract class MessageBench implements Bench {
        protected final Random random = new Random();

        public void operation() {
            int roll = random.nextInt(100);
            if (roll < 18) {
                addUserTransaction();
            } else if (roll < 45) {
                addPostTransaction();
            } else {
                readInboxTransaction();
            }
        }

        protected abstract void addUserTransaction();
        protected abstract void addPostTransaction();
        protected abstract void readInboxTransaction();
    }

    public static class Mixed extends MessageBench {
        private CassandraStoreBinding store;
        private final Ref<demos.message.consystop.Group>[] groups = new Ref[nGroups];
        private final Ref<demos.message.consystop.User>[] users = new Ref[nUsers];

        public void setup(int id) {
            if (id == 0) {
                store = Cassandra.newReplica("127.0.0.1", 9042, 2181, Duration.apply(msTimeout, "ms"), true);
                for (int i = 0; i < nGroups; i++) {
                    int finalI = i;
                    store.transaction(ctx -> {
                        groups[finalI] = ctx.replicate("group" + finalI, MIXED, demos.message.consystop.Group.class);
                        return Option.empty();
                    });
                }
                for (int i = 0; i < nUsers; i++) {
                    int finalI = i;
                    store.transaction(ctx -> {
                        users[finalI] = ctx.replicate("user" + finalI, MIXED, demos.message.consystop.User.class, "user" + finalI);
                        return Option.empty();
                    });
                }
            } else {
                store = Cassandra.newReplica("127.0.0." + (id+1), 9042, 2181, Duration.apply(msTimeout, "ms"), false);
                for (int i = 0; i < nGroups; i++) {
                    int finalI = i;
                    store.transaction(ctx -> {
                        groups[finalI] = ctx.lookup("group" + finalI, MIXED, demos.message.consystop.Group.class);
                        return Option.empty();
                    });
                }
                for (int i = 0; i < nUsers; i++) {
                    int finalI = i;
                    store.transaction(ctx -> {
                        users[finalI] = ctx.lookup("user" + finalI, MIXED, demos.message.consystop.User.class);
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

        protected void addUserTransaction() {
            int g = random.nextInt(groups.length);
            int u = random.nextInt(users.length);
            doTransaction(() -> {
                store.transaction(ctx -> {
                    groups[g].ref().addUser(users[u]);
                    return Option.empty();
                });
                return null;
            }, msRetry);
        }

        protected void addPostTransaction() {
            int g = random.nextInt(groups.length);
            doTransaction(() -> {
                store.transaction(ctx -> {
                    groups[g].ref().addPost("Hello" + g);
                    return Option.empty();
                });
                return null;
            }, msRetry);
        }

        protected void readInboxTransaction() {
            int u = random.nextInt(users.length);
            doTransaction(() -> {
                store.transaction(ctx -> {
                    users[u].ref().getInbox();
                    return Option.empty();
                });
                return null;
            }, msRetry);
        }
    }

    public static class Mono extends MessageBench {
        private CassandraStoreBinding store;
        private final Ref<demos.message.consyst.Group>[] groups = new Ref[nGroups];
        private final Ref<demos.message.consyst.User>[] users = new Ref[nUsers];
        private final Ref<demos.message.consyst.Inbox>[] inboxes = new Ref[nUsers];

        public void setup(int id) {
            if (id == 0) {
                store = Cassandra.newReplica("127.0.0.1", 9042, 2181, Duration.apply(100, "ms"), true);
                for (int i = 0; i < nGroups; i++) {
                    int finalI = i;
                    store.transaction(ctx -> {
                        groups[finalI] = ctx.replicate("group" + finalI, STRONG, demos.message.consyst.Group.class);
                        return Option.empty();
                    });
                }
                for (int i = 0; i < nUsers; i++) {
                    int finalI = i;
                    store.transaction(ctx -> {
                        inboxes[finalI] = ctx.replicate("inbox" + finalI, STRONG, demos.message.consyst.Inbox.class);
                        users[finalI] = ctx.replicate("user" + finalI, WEAK, demos.message.consyst.User.class, inboxes[finalI], "user" + finalI);
                        return Option.empty();
                    });
                }
            } else {
                store = Cassandra.newReplica("127.0.0." + (id+1), 9042, 2181, Duration.apply(100, "ms"), false);
                for (int i = 0; i < nGroups; i++) {
                    int finalI = i;
                    store.transaction(ctx -> {
                        groups[finalI] = ctx.lookup("group" + finalI, STRONG, demos.message.consyst.Group.class);
                        return Option.empty();
                    });
                }
                for (int i = 0; i < nUsers; i++) {
                    int finalI = i;
                    store.transaction(ctx -> {
                        inboxes[finalI] = ctx.lookup("inbox" + finalI, STRONG, demos.message.consyst.Inbox.class);
                        users[finalI] = ctx.lookup("user" + finalI, WEAK, demos.message.consyst.User.class);
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

        protected void addUserTransaction() {
            int g = random.nextInt(groups.length);
            int u = random.nextInt(users.length);
            doTransaction(() -> {
                store.transaction(ctx -> {
                    groups[g].ref().addUser(users[u]);
                    return Option.empty();
                });
                return null;
            }, msRetry);
        }

        protected void addPostTransaction() {
            int g = random.nextInt(groups.length);
            doTransaction(() -> {
                store.transaction(ctx -> {
                    groups[g].ref().addPost("Hello" + g);
                    return Option.empty();
                });
                return null;
            }, msRetry);
        }

        protected void readInboxTransaction() {
            int u = random.nextInt(users.length);
            doTransaction(() -> {
                store.transaction(ctx -> {
                    users[u].ref().getInbox();
                    return Option.empty();
                });
                return null;
            }, msRetry);
        }
    }
}
