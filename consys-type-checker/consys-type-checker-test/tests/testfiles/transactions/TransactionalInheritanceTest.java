package de.tuda.stg.consys.checker.testfiles.testfiles.transactions;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraStoreBinding;
import scala.Option;

/**
 * Tests inheritance rules of @Transactional methods.
 */
class TransactionalTest {

    static class Base {
        @Transactional
        void f1() {}

        void f2() {}
    }

    static class DerivedSame extends Base {
        @Transactional
        @Override
        void f1() {}

        @Override
        void f2() {}
    }

    static class DerivedSameWithoutOverride extends Base {
        @Transactional
        void f1() {}

        void f2() {}
    }

    static class DerivedNonTransactional extends Base {
        @Override
        void f1() {}

        @Override
        void f2() {}
    }

    static class DerivedTransactional extends Base {
        @Transactional
        @Override
        void f1() {}

        @Transactional
        @Override
        // :: error: (transaction.override)
        void f2() {}
    }
}
