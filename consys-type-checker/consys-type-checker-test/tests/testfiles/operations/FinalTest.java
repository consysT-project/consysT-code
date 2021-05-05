package testfiles.operations;

import de.tuda.stg.consys.annotations.*;
import de.tuda.stg.consys.annotations.methods.*;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;

import java.io.Serializable;
// @skip-test
/**
 * Checks that fields that are never written are @Local
 */
public class FinalTest {
    static @Mixed
    class A implements Serializable {
        final int a;
        final int b = 0;
        int c;

        A() {
            a = 0;
        }

        @WeakOp
        int weak() { return c; }

        @StrongOp
        int strong() { return c; }

        @StrongOp
        void bla(@Local int l) {
            // checks that a, b, c are all @Local
            l = a;
            l = b;
            l = c;
        }
    }
}
