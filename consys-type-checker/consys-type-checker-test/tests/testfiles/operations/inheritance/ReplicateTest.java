package testfiles.operations.inheritance;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.Ref;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraConsistencyLevels;
import de.tuda.stg.consys.japi.binding.cassandra.CassandraTransactionContextBinding;

import java.io.Serializable;

public class ReplicateTest {
    static @Mixed class Base implements Serializable {
        void f() {}
    }
    static @Mixed class Derived extends Base {
        @Override void f() {}
    }

    @Transactional
    void func(Ref<Base> base) {
        base.ref().f();
    }

    @Transactional
    void generate(CassandraTransactionContextBinding ctx) {
        ctx.replicate("derived", CassandraConsistencyLevels.MIXED, Derived.class);
        Ref<Base> base = ctx.lookup("derived", CassandraConsistencyLevels.MIXED, Base.class);
        func(base);
    }
}

class Case1 {
    static @Mixed class Base implements Serializable {
        int i;

        @StrongOp
        void f() {
            i = 0;
        }
        @StrongOp
        @Strong int getI() {
            return i;
        }
    }

    static @Mixed class Derived extends Base {
        @WeakOp
        void g() {
            i = 0; // base class field is weakened in derived class
        }
    }
}

class Case2 {
    static @Mixed class Base implements Serializable {
        int i;

        @StrongOp
        void f() {
            i = 0;
        }

        @StrongOp
        @Strong int getI() {
            return i;
        }
    }

    static @Mixed class Derived extends Case1.Base {
        @Override
        @WeakOp
        void f() {
            i = 0; // base class field is weakened in derived class
        }
    }
}

// TODO: base class field is "removed" in derived class
