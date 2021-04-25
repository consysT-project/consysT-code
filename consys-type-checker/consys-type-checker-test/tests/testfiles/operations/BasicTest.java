import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.core.store.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.core.store.cassandra.levels.CassandraConsistencyLevel;
import de.tuda.stg.consys.japi.next.Ref;
import de.tuda.stg.consys.japi.next.TransactionContext;
import de.tuda.stg.consys.japi.next.binding.Cassandra;

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
            this.j = i;
        }
    }

    @Transactional
    void transaction(Cassandra.TransactionContextBinding ctx) {
        Ref<A> o = ctx.replicate("bla", CassandraConsistencyLevels.STRONG(), A.class);
    }
}
