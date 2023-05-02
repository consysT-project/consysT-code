package de.tuda.stg.consys.demo.messagegroups.schema;

import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.core.store.cassandra.levels.Strong$;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraReplica;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import scala.Option;
import scala.concurrent.duration.Duration;

import java.util.Optional;

public class Main {

    public static void main(String[] args) {
        CassandraStoreBinding store =
                CassandraReplica.create("127.0.0.1", 9042, 2181, Duration.apply(60, "s"), true);

        User user = new User("user");

        store.transaction((tx) -> {
            Ref<@Mutable @Weak User> user1 = tx.replicate("user1", CassandraConsistencyLevels.WEAK, User.class, "Alice");
            Ref<@Mutable @Strong User> user2 = tx.replicate("user2", CassandraConsistencyLevels.STRONG, User.class, "Bob");

//            user2.ref().name = user.name;

            return Option.apply(0);
        });
    }
}
