package de.tuda.stg.consys.demo.groupchat.schema;

import de.tuda.stg.consys.checker.qual.Immutable;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.core.store.CoordinationMechanism;
import de.tuda.stg.consys.demo.groupchat.schema.bank.BankAccount;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraReplica;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import scala.Option;
import scala.concurrent.duration.Duration;

public class Main {

    public static void main(String[] args) {
        System.out.println("0");

        CassandraStoreBinding store =
                CassandraReplica.create("127.0.0.1", 9042, new CoordinationMechanism.Zookeeper(2181), Duration.apply(60, "s"), true);

        System.out.println("1");

        store.transaction(tx -> {
            Ref<@Mutable @Weak User> user1 = tx.replicate("user1", CassandraConsistencyLevels.WEAK, User.class, "Alice");
            Ref<@Mutable @Strong User> user2 = tx.replicate("user2", CassandraConsistencyLevels.STRONG, User.class, "Bob");

//            user2.ref().name = user.name;

            return Option.apply(0);
        });

        System.out.println("2");
        @Immutable Option<Integer> res = store.transaction(tx -> {
           Ref<@Mutable BankAccount> acc1 = tx.replicate("acc1", CassandraConsistencyLevels.MIXED, BankAccount.class) ;
           acc1.ref().deposit(1000);
           acc1.ref().deposit(500);
           acc1.ref().withdraw(700);
           var bal = acc1.ref().balance();
           return Option.apply(bal);
        });

        System.out.println("3");

        System.out.println(res);

    }
}
