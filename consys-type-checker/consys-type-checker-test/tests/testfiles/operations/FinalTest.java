package testfiles.operations;

import de.tuda.stg.consys.annotations.*;
import de.tuda.stg.consys.annotations.methods.*;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;

import java.io.Serializable;

/**
 * Checks that fields that are never written are @Local
 */
public @Mixed class FinalTest {
    final int a;
    final int b = 0;
    int c;

    FinalTest() {
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
