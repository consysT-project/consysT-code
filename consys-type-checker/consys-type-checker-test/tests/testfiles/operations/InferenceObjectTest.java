import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.checker.qual.*;

/**
 * Check that reference type fields are inferred even when access happens to field of field
 */
public @Mixed class InferenceObjectTest {
    static class Box { int value; }
    static class BoxBox { Box value; }

    private Box box; // inferred @Strong
    private BoxBox boxBox; // inferred @Strong

    @StrongOp
    void writeBox() {
        box.value = 0;
        boxBox.value.value = 0;
    }

    @StrongOp
    void test() {
        @Immutable @Strong Box b = this.box;
        // :: error: assignment.type.incompatible
        @Immutable @Local Box b1 = this.box;

        @Strong int i = this.box.value;
        // :: error: assignment.type.incompatible
        @Local int i1 = this.box.value;

        b = this.boxBox.value;
        // :: error: assignment.type.incompatible
        b1 = this.boxBox.value;

        i = this.boxBox.value.value;
        // :: error: assignment.type.incompatible
        i1 = this.boxBox.value.value;
    }
}
