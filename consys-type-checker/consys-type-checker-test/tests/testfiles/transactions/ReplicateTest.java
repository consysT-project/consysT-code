package de.tuda.stg.consys.checker.testfiles.testfiles.transactions;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;
import scala.Option;

import java.io.Serializable;

/**
 * Tests the invocation of replicate and lookup operations inside and outside of transaction contexts.
 */
public class ReplicateTest {
    CassandraStoreBinding replica;
    CassandraTransactionContextBinding transaction;

    static class A implements Serializable { }

    void testReplicateInsideTransaction() {
        replica.transaction(ctx -> {
            Ref<@Strong A> x = ctx.replicate("obj1", CassandraConsistencyLevels.STRONG, A.class);
            Ref<@Strong A> y = ctx.lookup("obj1", CassandraConsistencyLevels.STRONG, A.class);
            return Option.empty();
        });
    }

    @Transactional
    void testReplicateInsideTransactionalMethod() {
        Ref<@Strong A> x = transaction.replicate("obj1", CassandraConsistencyLevels.STRONG, A.class);
        Ref<@Strong A> y = transaction.lookup("obj1", CassandraConsistencyLevels.STRONG, A.class);
    }

    void testReplicateOutsideTransaction() {
        // :: error: (invocation.replicate.transaction)
        Ref<@Strong A> x = transaction.replicate("obj1", CassandraConsistencyLevels.STRONG, A.class);
        // :: error: (invocation.replicate.transaction)
        Ref<@Strong A> y = transaction.lookup("obj1", CassandraConsistencyLevels.STRONG, A.class);
    }

    // Checks that @Transactional does not break other annotations
    @Deprecated
    void testReplicateOutsideTransactionalMethod() {
        // :: error: (invocation.replicate.transaction)
        Ref<@Strong A> x = transaction.replicate("obj1", CassandraConsistencyLevels.STRONG, A.class);
        // :: error: (invocation.replicate.transaction)
        Ref<@Strong A> y = transaction.lookup("obj1",  CassandraConsistencyLevels.STRONG, A.class);
    }
}