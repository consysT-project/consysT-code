package testfiles.operations.inheritance;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Inconsistent;
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
    static @Mixed class Base {
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
            // :: error: mixed.inheritance.field.overwrite
            i = 0; // base class field is weakened in derived class
        }
    }
}

class Case2 {
    static @Mixed class Base {
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
            // :: error: mixed.inheritance.field.overwrite
            i = 0; // base class field is weakened in override
        }
    }
}

// base class field is "removed" in derived class, i.e. derived class makes field stronger
class Case3 {
    static @Mixed class Base {
        int i;

        @WeakOp
        void f() {
            i = 0;
        }
    }

    static @Mixed class Derived extends Base {
        @Override
        void f() { }

        @StrongOp
        void g() {
            // field could be strong in derived -> ignored, field stays weak
            i = (@Weak int)0;
            // :: error: assignment.type.incompatible
            i = (@Inconsistent int)0;
        }
    }
}

// derived class makes field stronger
class Case4 {
    static @Mixed class Base {
        int i;

        @WeakOp
        void f() {
            i = 0;
        }
    }

    static @Mixed class Derived extends Base {
        @Override
        @StrongOp
        void f() {
            // base class field is made stronger by override -> ignored, field stays weak
            i = (@Weak int)0;
            // :: error: assignment.type.incompatible
            i = (@Inconsistent int)0;
        }
    }
}
