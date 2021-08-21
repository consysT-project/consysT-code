import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.checker.qual.*;
import de.tuda.stg.consys.japi.Ref;

public @Mixed class AInferenceObjectTest {
    static class Box { int value; }

    private Box box;

    @StrongOp
    void writeBox() {
        box.value = 0;
    }

    @Transactional static void test(Ref<@Immutable @Mixed AInferenceObjectTest> obj) {
        @Strong Box b = obj.ref().box;
        // :: error: assignment.type.incompatible
        @Local Box b1 = obj.ref().box;
    }
}
