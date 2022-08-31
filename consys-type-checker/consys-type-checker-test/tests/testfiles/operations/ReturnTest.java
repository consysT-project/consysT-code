import de.tuda.stg.consys.annotations.ThisConsistent;
import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;

/**
 * Tests return type 'inference' for mixed operations.
 * Return types default to the operation level if the return type is @Poly.
 */
// :: error: consistency.type.use.incompatible
public @Mixed class ReturnTest {
    protected @Strong int i;
    protected @Weak int j;

    @StrongOp
    public @ThisConsistent int getStrong() {
        return i;
    }

    @WeakOp
    public @ThisConsistent int getWeak() {
        return i;
    }

    public @ThisConsistent int get() {
        return i;
    }

    @StrongOp
    public @ThisConsistent int getError() {
        // :: error: return
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

        // :: error: assignment
        a = objStrong.ref().getWeak();
        // :: error: assignment
        a = objWeak.ref().getWeak();

        a = objStrong.ref().get();
        // :: error: assignment
        a = objWeak.ref().get();

        // :: error: assignment
        a = objStrong.ref().getExplicit();
    }
}

// :: error: consistency.type.use.incompatible
@Mixed class Derived extends ReturnTest {
    @StrongOp public @ThisConsistent int getStrong() {
        // :: error: return
        return j;
    }

    @WeakOp public @ThisConsistent int get() {
        return i;
    }

    @Transactional static void test2(Ref<@Mutable @Mixed(WeakOp.class) Derived> objWeak,
                                    Ref<@Mutable @Mixed(StrongOp.class) Derived> objStrong) { }
}
