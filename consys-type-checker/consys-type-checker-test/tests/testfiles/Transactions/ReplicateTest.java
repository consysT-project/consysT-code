package Transactions;

import de.tuda.stg.consys.checker.qual.Transactional;
import de.tuda.stg.consys.core.store.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.next.Ref;
import de.tuda.stg.consys.japi.binding.Cassandra;
import scala.Option;
import java.io.Serializable;

/**
 * Tests the invocation of replicate and lookup operations inside and outside of transaction contexts.
 */
public class ReplicateTest {
    Cassandra.ReplicaBinding replica;
    Cassandra.TransactionContextBinding transaction;

    static class A implements Serializable { }

    void testReplicateInsideTransaction() {
        replica.transaction(ctx -> {
            Ref<@Strong A> x = ctx.replicate("obj1", CassandraConsistencyLevels.STRONG(), A.class);
            Ref<@Strong A> y = ctx.lookup("obj1", A.class, CassandraConsistencyLevels.STRONG());
            return Option.empty();
        });
    }

    @Transactional
    void testReplicateInsideTransactionalMethod() {
        Ref<@Strong A> x = transaction.replicate("obj1", CassandraConsistencyLevels.STRONG(), A.class);
        Ref<@Strong A> y = transaction.lookup("obj1", A.class, CassandraConsistencyLevels.STRONG());
    }

    void testReplicateOutsideTransaction() {
        // :: error: (invocation.replicate.transaction)
        Ref<@Strong A> x = transaction.replicate("obj1", CassandraConsistencyLevels.STRONG(), A.class);
        // :: error: (invocation.replicate.transaction)
        Ref<@Strong A> y = transaction.lookup("obj1", A.class, CassandraConsistencyLevels.STRONG());
    }

    // Checks that @Transactional does not break other annotations
    @Deprecated
    void testReplicateOutsideTransactionalMethod() {
        // :: error: (invocation.replicate.transaction)
        Ref<@Strong A> x = transaction.replicate("obj1", CassandraConsistencyLevels.STRONG(), A.class);
        // :: error: (invocation.replicate.transaction)
        Ref<@Strong A> y = transaction.lookup("obj1", A.class, CassandraConsistencyLevels.STRONG());
    }
}