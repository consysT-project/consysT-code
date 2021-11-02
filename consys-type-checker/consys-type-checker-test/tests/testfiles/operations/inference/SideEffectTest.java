import de.tuda.stg.consys.annotations.methods.*;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.*;
import org.checkerframework.dataflow.qual.SideEffectFree;

/**
 * Tests SideEffectFree for mixed field inference.
 */
public @Mixed class SideEffectTest {
    static class Box {
        private int i;
        void set() { i = 0; }
        @SideEffectFree
        int get() { return i; }
    }

    private Box box; // inferred strong

    @StrongOp
    void callSideEffect() {
        box.set();
    }

    @WeakOp
    void callSideEffectFree() {
        box.get();
    }

    @StrongOp
    void test() {
        // :: error: assignment
        @Immutable @Local Box b1 = box; // box is inferred strong
        @Immutable @Strong Box b2 = box;
    }
}
