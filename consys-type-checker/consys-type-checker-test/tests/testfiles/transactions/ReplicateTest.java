package de.tuda.stg.consys.checker.testfiles.testfiles.transactions;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.akka.AkkaConsistencyLevels;
import de.tuda.stg.consys.japi.binding.akka.AkkaStoreBinding;
import de.tuda.stg.consys.japi.binding.akka.AkkaTransactionContextBinding;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;
import scala.Option;

import java.io.Serializable;

/**
 * Tests the invocation of replicate and lookup operations inside and outside of transaction contexts.
 */
public class ReplicateTest {
    CassandraStoreBinding replica0;
    CassandraTransactionContextBinding transaction0;
    AkkaStoreBinding replica1;
    AkkaTransactionContextBinding transaction1;

    static class A implements Serializable { }

    void testReplicateInsideTransaction() {
        replica0.transaction(ctx -> {
            Ref<@Strong A> x = ctx.replicate("obj1", CassandraConsistencyLevels.STRONG, A.class);
            Ref<@Strong A> y = ctx.lookup("obj1", CassandraConsistencyLevels.STRONG, A.class);
            return Option.empty();
        });

        replica1.transaction(ctx -> {
            Ref<@Strong A> x1 = ctx.replicate("obj1", AkkaConsistencyLevels.STRONG, A.class);
            Ref<@Strong A> y1 = ctx.lookup("obj1", AkkaConsistencyLevels.STRONG, A.class);
            return Option.empty();
        });
    }

    @Transactional
    void testReplicateInsideTransactionalMethod() {
        Ref<@Strong A> x = transaction0.replicate("obj1", CassandraConsistencyLevels.STRONG, A.class);
        Ref<@Strong A> y = transaction0.lookup("obj1", CassandraConsistencyLevels.STRONG, A.class);

        Ref<@Strong A> x1 = transaction1.replicate("obj1", AkkaConsistencyLevels.STRONG, A.class);
        Ref<@Strong A> y1 = transaction1.lookup("obj1", AkkaConsistencyLevels.STRONG, A.class);
    }

    void testReplicateOutsideTransaction() {
        // :: error: (invocation.replicate.transaction)
        Ref<@Strong A> x = transaction0.replicate("obj1", CassandraConsistencyLevels.STRONG, A.class);
        // :: error: (invocation.replicate.transaction)
        Ref<@Strong A> y = transaction0.lookup("obj1", CassandraConsistencyLevels.STRONG, A.class);

        // :: error: (invocation.replicate.transaction)
        Ref<@Strong A> x1 = transaction1.replicate("obj1", AkkaConsistencyLevels.STRONG, A.class);
        // :: error: (invocation.replicate.transaction)
        Ref<@Strong A> y1 = transaction1.lookup("obj1", AkkaConsistencyLevels.STRONG, A.class);
    }

    // Checks that @Transactional does not break other annotations
    @Deprecated
    void testReplicateOutsideTransactionalMethod() {
        // :: error: (invocation.replicate.transaction)
        Ref<@Strong A> x = transaction0.replicate("obj1", CassandraConsistencyLevels.STRONG, A.class);
        // :: error: (invocation.replicate.transaction)
        Ref<@Strong A> y = transaction0.lookup("obj1",  CassandraConsistencyLevels.STRONG, A.class);

        // :: error: (invocation.replicate.transaction)
        Ref<@Strong A> x1 = transaction1.replicate("obj1", AkkaConsistencyLevels.STRONG, A.class);
        // :: error: (invocation.replicate.transaction)
        Ref<@Strong A> y1 = transaction1.lookup("obj1",  AkkaConsistencyLevels.STRONG, A.class);
    }
}