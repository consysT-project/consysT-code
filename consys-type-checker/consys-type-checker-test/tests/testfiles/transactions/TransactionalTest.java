package de.tuda.stg.consys.checker.testfiles.testfiles.transactions;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import scala.Option;

/**
 * Tests the invocation of annotated @Transactional methods inside and outside of transaction contexts.
 * Checks that method overloading and overriding is resolved correctly.
 */
class TransactionalTest {

    static class Base {
        @Transactional
        void f1() {}
        @Transactional
        void f2() {}
        void f3() {}

        @Transactional
        int g1() { return 0; }
        @Transactional
        @Strong int g2() { return 0; }

        @Transactional
        void o1() {}
        void o1(int i) {}

        void o2() {}
        @Transactional
        void o2(int i) {}
    }

    static class Derived extends Base {
        @Transactional
        @Override
        void f1() {}

        @Override
        void f2() {}

        @Transactional
        @Override
        void f3() {}
    }

    void testTransactionalInvocation_OutsideTransaction(Base base, Derived derived) {
        // :: error: (invocation.method.transaction)
        base.f1();
        // :: error: (invocation.method.transaction)
        base.f2();
        base.f3();

        // :: error: (invocation.method.transaction)
        base.g1();
        // :: error: (invocation.method.transaction)
        base.g2();

        // :: error: (invocation.method.transaction)
        base.o1();
        base.o1(0);

        base.o2();
        // :: error: (invocation.method.transaction)
        base.o2(0);

        // :: error: (invocation.method.transaction)
        derived.f1();
        derived.f2();
        // :: error: (invocation.method.transaction)
        derived.f3();
    }

    @Transactional
    void testTransactionalInvocation_InsideTransactional(Base base, Derived derived) {
        base.f1();
        base.f2();
        base.f3();

        base.g1();
        base.g2();

        base.o1();
        base.o1(0);

        base.o2();
        base.o2(0);

        derived.f1();
        derived.f2();
        derived.f3();
    }


    void testTransactionalInvocation_InsideTransaction(Base base, Derived derived, CassandraStoreBinding replica) {
        replica.transaction(ctx -> {
            base.f1();
            base.f2();
            base.f3();

            base.g1();
            base.g2();

            base.o1();
            base.o1(0);

            base.o2();
            base.o2(0);

            derived.f1();
            derived.f2();
            derived.f3();

            return Option.empty();
        });
    }
}
