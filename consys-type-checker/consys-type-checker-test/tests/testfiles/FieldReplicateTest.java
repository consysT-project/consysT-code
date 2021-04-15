package de.tuda.stg.consys.checker.testfiles.testfiles;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;

import java.io.Serializable;

/**
 * Tests replication of classes with fields that would lead to data flow errors under specific levels.
 */
public class FieldReplicateTest {
    CassandraTransactionContextBinding transaction;

    // A can be replicated at level @Strong and @Weak
    static class A implements Serializable {
        int i;
        void m(@Strong int j){
            i = j;
        }
    }

    // B can only be replicated at level @Weak
    static class B implements Serializable {
        int i;
        void m(@Weak int j){
            // replication of B at level @Strong would lead to a flow error here, so it should be disallowed
            i = j;
        }
    }

    @Transactional
    void testReplicateA() {
        // replication of A at level @Weak is allowed
        transaction.replicate("", CassandraConsistencyLevels.WEAK, (Class<@Weak A>)A.class);

        // replication of A at level @Strong is allowed
        transaction.replicate("", CassandraConsistencyLevels.STRONG, (Class<@Strong A>)A.class);
    }

    @Transactional
    void testReplicateB() {
        // replication of B at level @Weak is allowed
        transaction.replicate("", CassandraConsistencyLevels.WEAK, (Class<@Weak B>)B.class);

        // replication of B at level @Strong is disallowed
        // :: error: (replicate.class)
        transaction.replicate("", CassandraConsistencyLevels.STRONG, (Class<@Strong B>)B.class);
    }
}
