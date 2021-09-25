import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;

/**
 * Tests that using fields transitively by assigning them to other fields does not break mixed type rules.
 */
public @Mixed class TransitiveObjectTest {
    static class Box {
        int value;
    }

    private @Strong Box strongBox;
    private @Strong Box otherStrongBox;
    private @Weak Box weakBox;
    private @Weak Box otherWeakBox;

    @WeakOp void test() {
        // :: error: assignment
        weakBox = strongBox;
        weakBox.value = 0;
    }

    @StrongOp void test2() {
        // :: error: assignment
        strongBox = weakBox;
        strongBox.value = 0;

        otherWeakBox = weakBox;
        otherStrongBox = strongBox;
    }
}
