package de.tuda.stg.consys.checker.testfiles.testfiles.transactions;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import scala.Option;

import java.io.Serializable;

/**
 * Tests the invocation of ref operations inside and outside of transaction contexts.
 */
public class RefTest {
    CassandraStoreBinding replica;
    Ref<@Strong A> obj;

    static class A implements Serializable {
        int n;
        void f() {}
    }

    void testRefInsideTransaction() {
        replica.transaction(ctx -> {
            int n = obj.ref().n;
            obj.ref().n = 0;
            obj.ref().f();
            return Option.empty();
        });
    }

    @Transactional
    void testRefInsideTransactionalMethod() {
        int n = obj.ref().n;
        obj.ref().n = 0;
        obj.ref().f();
    }

    void testRefOutsideTransaction() {
        // :: error: (invocation.ref.transaction)
        int n = obj.ref().n;
        // :: error: (invocation.ref.transaction)
        obj.ref().n = 0;
        // :: error: (invocation.ref.transaction)
        obj.ref().f();
    }

    // Checks that @Transactional does not break other annotations
    @Deprecated
    void testRefOutsideTransactionalMethod() {
        // :: error: (invocation.ref.transaction)
        int n = obj.ref().n;
        // :: error: (invocation.ref.transaction)
        obj.ref().n = 0;
        // :: error: (invocation.ref.transaction)
        obj.ref().f();
    }
}