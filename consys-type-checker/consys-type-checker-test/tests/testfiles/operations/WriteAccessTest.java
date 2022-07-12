import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;

/**
 * Tests various write access expressions.
 */
public @Mixed class WriteAccessTest {
    private @Strong int i;

    @WeakOp
    void test() {
        // :: error: mixed.field.incompatible
        i = 0;

        // :: error: mixed.field.incompatible
        i++;

        // :: error: mixed.field.incompatible
        i += 1;

        // :: error: mixed.field.incompatible
        this.i = 0;

        // :: error: mixed.field.incompatible
        this.i++;

        // :: error: mixed.field.incompatible
        this.i += 1;
    }
}
