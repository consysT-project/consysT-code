package de.tuda.stg.consys.integrationtest;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.Cassandra;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import scala.Option;
import scala.concurrent.duration.Duration;

import java.io.Serializable;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

import static de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.MIXED;

public class MixedExample {

    public static class Register implements Serializable {
        private int i;

        public Register(int i) {
            this.i = i;
        }

        @StrongOp
        public void set(int i) {
            this.i = i;
        }

        @WeakOp
        public int get() {
            return this.i;
        }

        @StrongOp
        public void reset() {
            this.i = 0;
        }

        @WeakOp
        public void dbl() {
            this.i = this.i * 2;
        }
    }

    static class Process1 implements Runnable {
        CassandraStoreBinding store =
                Cassandra.newReplica("127.0.0.1", 9042, 2181, Duration.apply(60, "s"), true);

        @Override
        public void run() {
            try {
                System.out.println("Start Process 1");
                store.transaction(ctx -> {
                    ctx.replicate("register1", MIXED, (Class<@Mixed Register>) Register.class, 42);
                    return Option.apply(0);
                });

                store.transaction(ctx -> {
                    Ref<@Mixed Register> reg1 = ctx.lookup("register1", MIXED, (Class<@Mixed Register>) Register.class);
                    Ref<@Mixed Register> reg2 = ctx.lookup("register2", MIXED, (Class<@Mixed Register>) Register.class);
                    reg2.ref().set(33);
                    var value = reg1.ref().get();
                    return Option.apply(0);
                });

                store.transaction(ctx -> {
                    Ref<@Mixed Register> reg1 = ctx.lookup("register1", MIXED, (Class<@Mixed Register>) Register.class);
                    reg1.ref().reset();
                    return Option.apply(0);
                });

                store.transaction(ctx -> {
                    Ref<@Mixed Register> reg1 = ctx.lookup("register1", MIXED, (Class<@Mixed Register>) Register.class);
                    Ref<@Mixed Register> reg2 = ctx.lookup("register2", MIXED, (Class<@Mixed Register>) Register.class);
                    var value1 = reg1.ref().get();
                    var value2 = reg2.ref().get();
                    System.out.println("Process1: " + value1 + " / " + value2);
                    return Option.apply(0);
                });
            } catch (Exception e) {
                e.printStackTrace();
            }
        }
    }

    static class Process2 implements Runnable {
        CassandraStoreBinding store =
                Cassandra.newReplica("127.0.0.2", 9042, 2182, Duration.apply(60, "s"), false);

        @Override
        public void run() {
            System.out.println("Start Process 2");
            store.transaction(ctx -> {
                ctx.replicate("register2", MIXED, (Class<@Mixed Register>) Register.class, 0);
                return Option.apply(0);
            });

            store.transaction(ctx -> {
                Ref<@Mixed Register> reg1 = ctx.lookup("register1", MIXED, (Class<@Mixed Register>) Register.class);
                reg1.ref().dbl();
                var value = reg1.ref().get();
                System.out.println(value);
                return Option.apply(0);
            });

            store.transaction(ctx -> {
                Ref<@Mixed Register> reg1 = ctx.lookup("register1", MIXED, (Class<@Mixed Register>) Register.class);
                reg1.ref().set(-1);
                reg1.ref().dbl();
                return Option.apply(0);
            });

            store.transaction(ctx -> {
                Ref<@Mixed Register> reg2 = ctx.lookup("register2", MIXED, (Class<@Mixed Register>) Register.class);
                reg2.ref().set(123456);
                return Option.apply(0);
            });

            store.transaction(ctx -> {
                Ref<@Mixed Register> reg1 = ctx.lookup("register1", MIXED, (Class<@Mixed Register>) Register.class);
                Ref<@Mixed Register> reg2 = ctx.lookup("register2", MIXED, (Class<@Mixed Register>) Register.class);
                var value1 = reg1.ref().get();
                var value2 = reg2.ref().get();
                System.out.println("Process2: " + value1 + " / " + value2);
                return Option.apply(0);
            });
        }
    }

    public static void main(String[] args) throws InterruptedException {
        var pool = Executors.newFixedThreadPool(2);

        System.out.println("=== Create processes ===");
        var process1 = new Process1();
        var process2 = new Process2();

        System.out.println("=== Submit processes ===");
        pool.submit(process1);
        pool.submit(process2);

        pool.shutdown();
        pool.awaitTermination(60, TimeUnit.SECONDS);
        System.out.println("=== Shutdown ===");
    }


}
