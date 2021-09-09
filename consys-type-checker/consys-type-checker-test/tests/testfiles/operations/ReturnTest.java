package testfiles.operations;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;

public @Mixed class ReturnTest {
    protected @Strong int i;
    protected @Weak int j;

    @StrongOp
    public int getStrong() {
        return i;
    }

    @WeakOp
    public int getWeak() {
        return i;
    }

    public int get() {
        return i;
    }

    @StrongOp
    public int getError() {
        // :: error: return.type.incompatible
        return j;
    }

    @StrongOp
    public @Inconsistent int getExplicit() {
        return i;
    }

    @Transactional static void test(Ref<@Mutable @Mixed(WeakOp.class) ReturnTest> objWeak,
                                    Ref<@Mutable @Mixed(StrongOp.class) ReturnTest> objStrong) {
        @Strong int a;
        a = objStrong.ref().getStrong();
        a = objWeak.ref().getStrong();

        // :: error: assignment.type.incompatible
        a = objStrong.ref().getWeak();
        // :: error: assignment.type.incompatible
        a = objWeak.ref().getWeak();

        a = objStrong.ref().get();
        // :: error: assignment.type.incompatible
        a = objWeak.ref().get();

        // :: error: assignment.type.incompatible
        a = objStrong.ref().getExplicit();
    }
}

@Mixed class Derived extends ReturnTest {
    @StrongOp public int getStrong() {
        // :: error: return.type.incompatible
        return j;
    }

    // :: error: override.return.invalid
    @WeakOp public int get() {
        return i;
    }

    @Transactional static void test2(Ref<@Mutable @Mixed(WeakOp.class) Derived> objWeak,
                                    Ref<@Mutable @Mixed(StrongOp.class) Derived> objStrong) { }
}
