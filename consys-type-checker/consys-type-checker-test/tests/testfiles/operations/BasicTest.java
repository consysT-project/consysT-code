import de.tuda.stg.consys.annotations.*;
import de.tuda.stg.consys.annotations.methods.*;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;
import org.checkerframework.framework.qual.DefaultQualifierForUse;

import java.io.Serializable;
//@skip-test
public class BasicTest {
    @Transactional
    void transaction(@Mutable CassandraTransactionContextBinding ctx, AA z) {
        Ref<@Mixed @Mutable B> b = ctx.replicate("o", CassandraConsistencyLevels.MIXED, (Class<@Mixed @Mutable B>) B.class);
        Ref<@Mixed @Mutable AA> o = ctx.lookup("o", CassandraConsistencyLevels.MIXED, (Class<@Mixed @Mutable AA>) AA.class);

        @Immutable @Mixed AA a = new AA();
        @Immutable @Weak AA aa = new AA();
        @Immutable @Strong AA aaa = new AA();

        AA aaaa = new AA();
        @Immutable @Strong AA aaaaa = aaaa;
    }
}

@DefaultQualifierForUse(Mixed.class)
@Mixed class B extends AA {@Strong int i; @Weak int j;}

@Mixed class AA implements Serializable {
    static class C { private int k; }

    @Strong B obj;

    private int j;

    @StrongOp
    void bla2(@Weak C o) {
        // :: error: assignment.type.incompatible
        this.j = o.k;

        obj = new B();
        @Strong int a = 0;
    }

    @WeakOp
    void blabla() {
        @Strong int a;
        // :: error: assignment.type.incompatible
        a = j;
    }
}
