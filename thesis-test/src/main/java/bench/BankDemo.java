package bench;

import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.Cassandra;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import scala.Option;
import scala.concurrent.duration.Duration;

import java.util.Random;
import java.util.List;

import static de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.*;

public class BankDemo {
    static final int nUsers = 100;
    static final long msTimeout = 100;
    static final long msRetry = 50;

    public static abstract class BankBench implements Bench {
        protected final Random random = new Random();

        public void operation() {
            int roll = random.nextInt(100);
            if (roll < 12) {
                sendMessageTransaction();
            } else if (roll < 28) {
                viewInboxTransaction();
            } else if (roll < 52) {
                transferTransaction();
            } else {
                viewBalanceTransaction();
            }
        }

        protected abstract void transferTransaction();
        protected abstract void sendMessageTransaction();
        protected abstract void viewBalanceTransaction();
        protected abstract void viewInboxTransaction();
    }

    public static class Mixed extends BankBench {
        private CassandraStoreBinding store;
        private Ref<demos.bank.consystop.Bank> bank;
        private Ref<demos.bank.consystop.User>[] users = new Ref[nUsers];

        public void setup(int id) {
            if (id == 0) {
                store = Cassandra.newReplica("127.0.0.1", 9042, 2181, Duration.apply(msTimeout, "ms"), true);
                store.transaction(ctx -> {
                    bank = ctx.replicate("bank", MIXED, demos.bank.consystop.Bank.class, "bank");
                    return Option.empty();
                });
                for (int i = 0; i < nUsers; i++) {
                    int finalI = i;
                    store.transaction(ctx -> {
                        users[finalI] = bank.ref().registerUser("user" + finalI, ctx);
                        if (finalI % 2 == 0) {
                            bank.ref().registerOverdraftAccount(users[finalI], ctx);
                        } else {
                            bank.ref().registerPrepaidAccount(users[finalI], ctx);
                        }
                        return Option.empty();
                    });
                }
                for (int i = 0; i < nUsers; i++) {
                    int finalI = i;
                    store.transaction(ctx -> {
                        ((Ref<? extends demos.bank.consystop.Account>)users[finalI].ref().getPrimaryAccount()).ref().deposit(1000);
                        return Option.empty();
                    });
                }
            } else {
                store = Cassandra.newReplica("127.0.0." + (id+1), 9042, 2181, Duration.apply(msTimeout, "ms"), false);
                store.transaction(ctx -> {
                    bank = ctx.lookup("bank", MIXED, demos.bank.consystop.Bank.class);
                    ((List<Ref<demos.bank.consystop.User>>)bank.ref().getUsers()).toArray(users);
                    return Option.empty();
                });
            }
        }

        public void shutdown() {
            try {
                store.close();
            } catch (Exception ignored) {}
        }

        protected void transferTransaction() {
            int s = random.nextInt(users.length);
            int r = random.nextInt(users.length);
            doTransaction(() -> {
                store.transaction(ctx -> {
                    ((Ref<? extends demos.bank.consystop.Account>)users[s].ref().getPrimaryAccount()).ref().deposit(1);
                    users[s].ref().transferTo(users[r], 1);
                   return Option.empty();
                });
                return null;
            }, msRetry);
        }

        protected void viewBalanceTransaction() {
            int u = random.nextInt(users.length);
            doTransaction(() -> {
                store.transaction(ctx -> {
                    ((demos.bank.consystop.User)users[u].ref()).getPrimaryAccount().ref().getBalance();
                    return Option.empty();
                });
                return null;
            }, msRetry);
        }

        protected void sendMessageTransaction() {
            doTransaction(() -> {
                store.transaction(ctx -> {
                    bank.ref().publishSystemMessage("dummy message");
                    return Option.empty();
                });
                return null;
            }, msRetry);
        }

        protected void viewInboxTransaction() {
            int u = random.nextInt(users.length);
            doTransaction(() -> {
                store.transaction(ctx -> {
                    ((demos.bank.consystop.User)users[u].ref()).getPrimaryAccount().ref().getInbox();
                    return Option.empty();
                });
                return null;
            }, msRetry);
        }
    }

    public static class Mono extends BankBench {
        private int id;
        private CassandraStoreBinding store;
        private Ref<demos.bank.consyst.Bank> bank;
        private Ref<demos.bank.consyst.User>[] users = new Ref[nUsers];

        public void setup(int id) {
            this.id = id;
            if (id == 0) {
                store = Cassandra.newReplica("127.0.0.1", 9042, 2181, Duration.apply(msTimeout, "ms"), true);
                store.transaction(ctx -> {
                    bank = ctx.replicate("bank", STRONG, demos.bank.consyst.Bank.class, "bank");
                    return Option.empty();
                });
                for (int i = 0; i < nUsers; i++) {
                    int finalI = i;
                    store.transaction(ctx -> {
                        users[finalI] = bank.ref().registerUser("user" + finalI, ctx);
                        if (finalI % 2 == 0) {
                            bank.ref().registerOverdraftAccount(users[finalI], ctx);
                        } else {
                            bank.ref().registerPrepaidAccount(users[finalI], ctx);
                        }
                        return Option.empty();
                    });
                }
                for (int i = 0; i < nUsers; i++) {
                    int finalI = i;
                    store.transaction(ctx -> {
                        ((Ref<? extends demos.bank.consyst.Account>)users[finalI].ref().getPrimaryAccount()).ref().deposit(1000);
                        return Option.empty();
                    });
                }
            } else {
                store = Cassandra.newReplica("127.0.0." + (id+1), 9042, 2181, Duration.apply(msTimeout, "ms"), false);
                store.transaction(ctx -> {
                    bank = ctx.lookup("bank", STRONG, demos.bank.consyst.Bank.class);
                    ((List<Ref<demos.bank.consyst.User>>)bank.ref().getUsers()).toArray(users);
                    return Option.empty();
                });
            }
        }

        public void shutdown() {
            try {
                store.close();
            } catch (Exception ignored) {}
        }

        protected void transferTransaction() {
            int s = random.nextInt(users.length);
            int r = random.nextInt(users.length);
            //System.out.println(id + ": start transfer " + s + "->" + r);
            doTransaction(() -> {
                store.transaction(ctx -> {
                    ((Ref<? extends demos.bank.consyst.Account>)users[s].ref().getPrimaryAccount()).ref().deposit(1);
                    users[s].ref().transferTo(users[r], 1);
                    return Option.empty();
                });
                return null;
            }, msRetry);
            //System.out.println(id + ": end transfer " + s + "->" + r);
        }

        protected void viewBalanceTransaction() {
            int u = random.nextInt(users.length);
            //System.out.println(id + ": start view balance " + u);
            doTransaction(() -> {
                store.transaction(ctx -> {
                    ((demos.bank.consyst.User)users[u].ref()).getPrimaryAccount().ref().getBalance();
                    return Option.empty();
                });
                return null;
            }, msRetry);
            //System.out.println(id + ": end view balance " + u);
        }

        protected void sendMessageTransaction() {
            //System.out.println(id + ": start msg send");
            doTransaction(() -> {
                store.transaction(ctx -> {
                    bank.ref().publishSystemMessage("dummy message");
                    return Option.empty();
                });
                return null;
            }, msRetry);
            //System.out.println(id + ": end msg send");
        }

        protected void viewInboxTransaction() {
            int u = random.nextInt(users.length);
            //System.out.println(id + ": start view inbox " + u);
            doTransaction(() -> {
                store.transaction(ctx -> {
                    ((demos.bank.consyst.User)users[u].ref()).getPrimaryAccount().ref().getInbox();
                    return Option.empty();
                });
                return null;
            }, msRetry);
            //System.out.println(id + ": end view inbox " + u);
        }
    }
}
