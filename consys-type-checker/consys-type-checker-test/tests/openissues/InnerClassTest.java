package openissues;

import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;
import static  de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels.*;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;

import java.io.Serializable;

public @Mixed class InnerClassTest {
    private @Strong int i;

    public class Inner implements Serializable {
        private int j;
        void test() {
            i = 0;
        }
    }

    static void test(CassandraTransactionContextBinding ctx) {
        Ref<@Strong Inner> a = ctx.replicate("", STRONG, Inner.class);

        @Mixed InnerClassTest o = new @Mixed InnerClassTest() {

        };
    }
}
