package compiler;

import de.tuda.stg.consys.core.store.CoordinationMechanism;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraReplica;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import scala.Option;
import scala.concurrent.duration.Duration;

import java.io.Serializable;

public class TypeTest implements Serializable {
    public int x = 0;

    public static void main(String[] args) throws Exception {
        CassandraStoreBinding r0 = CassandraReplica.create("127.0.0.1", 9042, new CoordinationMechanism.Zookeeper(2181),
                Duration.apply(60000L, "ms"), true);

        r0.transaction(ctx -> {
            Ref<TypeTest> r = ctx.replicate("uut", CassandraConsistencyLevels.STRONG, TypeTest.class);

            // test correct type information for method invocation
            int i = r.ref().getInt() + r.ref().getInt();
            System.out.println(i);

            // test correct type information for fields
            r.ref().x = 42;
            int j = r.ref().x;
            System.out.println(j);

            // test compilation of multiple ref-call arguments
            r.ref().testArguments(r.ref().getInt(), r.ref().getString(), r.ref().getInt());

            return Option.empty();
        });

        r0.close();
    }

    public int getInt() {
        return 1;
    }

    public String getString() {
        return "hello";
    }

    public void testArguments(int a, String b, int c) {}
}
