package de.tuda.stg.consys.checker.testfiles.openissues;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import scala.Option;

import java.io.Serializable;


public class ReplicateReturnTest {
    CassandraStoreBinding replica;

    static class A implements Serializable { }

    void testReplicateInsideTransaction() {
        replica.transaction(ctx -> {
            Ref<@Strong A> x = ctx.replicate("obj1", CassandraConsistencyLevels.STRONG, A.class);
            Ref<@Strong A> y = ctx.lookup("obj1", CassandraConsistencyLevels.STRONG, A.class);
            //TODO should throw some kind of error, because we are assigning a WeakConsistencyLevel to a strong Ref.
            Ref<@Strong A> box = ctx.replicate("box", CassandraConsistencyLevels.WEAK, A.class);
            return Option.empty();
        });
    }
}