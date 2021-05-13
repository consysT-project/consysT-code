package testfiles.operations;

import de.tuda.stg.consys.annotations.*;
import de.tuda.stg.consys.annotations.methods.*;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;

import java.io.Serializable;

public class BasicTest {
    static @Mixed
    class A implements Serializable {
        static class B { int k; }

        int j;

        @StrongOp
        void bla2(@Weak B o) {
            // :: error: assignment.type.incompatible
            this.j = o.k;
        }
    }

    static @Mixed class B extends A {}

    @Transactional
    void transaction(CassandraTransactionContextBinding ctx) {
        // TODO: is this possible?
        ctx.replicate("o", CassandraConsistencyLevels.MIXED, B.class);
        Ref<A> o = ctx.lookup("o", CassandraConsistencyLevels.MIXED, A.class);
    }
}
