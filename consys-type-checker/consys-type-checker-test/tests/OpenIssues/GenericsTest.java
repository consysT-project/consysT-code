package OpenIssues;

import de.tuda.stg.consys.checker.qual.Transactional;
import de.tuda.stg.consys.core.store.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.next.Ref;
import de.tuda.stg.consys.japi.next.binding.Cassandra;
import scala.Option;
import java.io.Serializable;

public class GenericsTest {
    Cassandra.ReplicaBinding replica;
    Ref<@Strong A> obj;
    Ref<@Strong B> objB;

    static class A<T,U> implements Serializable {
        T t;
        U u;
        int n;

        void f() {
        }
    }

    static class B<@Weak T, @Strong U> implements Serializable {
        T t;
        U u;

        int n;

        void f() {
        }
    }

    void testRefInsideTransaction() {
        replica.transaction(ctx -> {
            int n = obj.ref().n;
            @Weak Object t = obj.ref().u;
            @Weak Object u1 = objB.ref().u;
            @Strong Object u2 = objB.ref().t;
            //obj.ref().n = 0;
            //obj.ref().f();
            return Option.empty();
        });
    }
}