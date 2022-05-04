import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.Immutable;
import de.tuda.stg.consys.checker.qual.Inconsistent;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.Cassandra;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;
import org.checkerframework.dataflow.qual.SideEffectFree;
import scala.Option;
import scala.concurrent.duration.Duration;

import java.io.PrintStream;
import java.io.Serializable;

public @Strong class Test implements Serializable {
    Test f;

    public static void main(String[] args) {
        CassandraStoreBinding r0 = (@Inconsistent @Mutable CassandraStoreBinding)Cassandra.newReplica("127.0.0.1", 9042, 2181, Duration.apply(60000L, "ms"), true);
        r0.transaction(ctx -> {
            Ref<Test> r = ctx.replicate("t", CassandraConsistencyLevels.STRONG, Test.class);

            @Strong int i = r.ref().getI() + r.ref().getI();

            ((@Mutable @Inconsistent PrintStream)System.out).println(i);
            return Option.empty();
        });

        try {
            r0.close();
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    @Transactional
    @SideEffectFree
    public @Strong int getI() {
        return 1;
    }
}
