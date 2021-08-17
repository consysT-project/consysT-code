import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.Immutable;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;

import java.io.Serializable;

public class ReplicateTest {
    static @Mixed class A implements Serializable { }

    static class B implements Serializable { }

    @Transactional
    void transaction(CassandraTransactionContextBinding ctx) {
        // replicate() parameters are all @Immutable @Inconsistent, and immutability assignments checks are disabled
        // replicate() arguments are:
        //      string literal is @MutableBottom @Local
        //      consistency level is a field, thus @Mutable @Inconsistent
        //      class literal is @MutableBottom @Local

        Ref<A> a = ctx.replicate("o", CassandraConsistencyLevels.MIXED, A.class);
        Ref<@Mutable A> a1 = ctx.replicate("o", CassandraConsistencyLevels.MIXED, A.class);
        Ref<@Immutable A> a2 = ctx.replicate("o", CassandraConsistencyLevels.MIXED, A.class);

        Ref<@Mixed B> b1 = ctx.replicate("o", CassandraConsistencyLevels.MIXED, B.class);
        Ref<@Mutable @Mixed B> b2 = ctx.replicate("o", CassandraConsistencyLevels.MIXED, B.class);
        Ref<@Immutable @Mixed B> b3 = ctx.replicate("o", CassandraConsistencyLevels.MIXED, B.class);
    }
}
