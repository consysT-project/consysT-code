package operations;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;

import java.io.Serializable;

public class ReplicateTest {
    static @Mixed class A implements Serializable {
        int i;
        void f() {
            i = 0;
        }
    }

    static class B implements Serializable {
        int a;
        void f() {
            a = 0;
        }
    }

    @Transactional
    void transaction(CassandraTransactionContextBinding ctx) {
        Ref<A> o = ctx.replicate("o", CassandraConsistencyLevels.MIXED, A.class);

        Ref<@Mixed B> u = ctx.replicate("o", CassandraConsistencyLevels.MIXED, B.class);
    }
}
