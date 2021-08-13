import de.tuda.stg.consys.annotations.*;
import de.tuda.stg.consys.annotations.methods.*;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;

import java.io.Serializable;

public class BasicTest {
    @Transactional
    void transaction(CassandraTransactionContextBinding ctx) {
        Ref<@Mixed B> b = ctx.replicate("o", CassandraConsistencyLevels.MIXED, (@Mixed Class<B>)B.class);
        Ref<@Mixed AA> o = ctx.lookup("o", CassandraConsistencyLevels.MIXED, (@Mixed Class<AA>)AA.class);
    }
}

@Mixed class B extends AA {}

@Mixed class AA implements Serializable {
    static class C { int k; }

    private int j;

    @StrongOp
    void bla2(@Weak C o) {
        // :: error: assignment.type.incompatible
        this.j = o.k;
    }

    @WeakOp
    void blabla() {
        @Strong int a;
        // :: error: assignment.type.incompatible
        a = j;
    }
}
