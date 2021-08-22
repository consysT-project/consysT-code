import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;

public @Mixed class InferenceObjectTest {
    static class Box { int value; }
    static class BoxBox { Box value; }

    private Box box;
    private BoxBox boxBox;

    @StrongOp
    void writeBox() {
        box.value = 0;
        boxBox.value.value = 0;
    }

    @Transactional static void test(Ref<@Immutable @Mixed InferenceObjectTest> obj) {
        @Strong Box b = obj.ref().box;
        // :: error: assignment.type.incompatible
        @Local Box b1 = obj.ref().box;
        @Strong int i = obj.ref().box.value;
        // :: error: assignment.type.incompatible
        @Local int i1 = obj.ref().box.value;

        b = obj.ref().boxBox.value;
        // :: error: assignment.type.incompatible
        b1 = obj.ref().boxBox.value;
        i = obj.ref().boxBox.value.value;
        // :: error: assignment.type.incompatible
        i1 = obj.ref().boxBox.value.value;
    }
}
