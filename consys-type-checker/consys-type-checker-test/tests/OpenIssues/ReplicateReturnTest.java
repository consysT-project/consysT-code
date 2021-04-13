package OpenIssues;

import de.tuda.stg.consys.core.store.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.next.Ref;
import de.tuda.stg.consys.japi.binding.Cassandra;
import scala.Option;
import java.io.Serializable;


public class ReplicateReturnTest {
    Cassandra.ReplicaBinding replica;

    static class A implements Serializable { }

    void testReplicateInsideTransaction() {
        replica.transaction(ctx -> {
            Ref<@Strong A> x = ctx.replicate("obj1", CassandraConsistencyLevels.STRONG(), A.class);
            Ref<@Strong A> y = ctx.lookup("obj1", A.class, CassandraConsistencyLevels.STRONG());
            //TODO should throw some kind of error, because we are assigning a WeakConsistencyLevel to a strong Ref.
            Ref<@Strong A> box = ctx.replicate("box", CassandraConsistencyLevels.WEAK(), A.class);
            return Option.empty();
        });
    }
}