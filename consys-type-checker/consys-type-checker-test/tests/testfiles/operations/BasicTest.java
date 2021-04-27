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
        int i;
        int j;

        @WeakOp
        int weak() { return i; }

        @StrongOp
        int strong() { return i + j; }

        @StrongOp
        void bla() {
            // :: error: assignment.type.incompatible
            this.j = i;
        }
    }

    @Transactional
    void transaction(CassandraTransactionContextBinding ctx) {
        Ref<A> o = ctx.replicate("o", CassandraConsistencyLevels.MIXED, A.class);
    }
}
