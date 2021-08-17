import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.Ref;

public class StaticTest {
    // :: error: mixed.field.static.incompatible
    static @Weak int i;
    static int j;

    @Transactional
    void test(Ref<@Mixed StaticTest> obj) {
        @Weak int a;
        // :: error: assignment.type.incompatible
        a = obj.ref().i;
        // :: error: assignment.type.incompatible
        a = StaticTest.i;
        // :: error: assignment.type.incompatible
        a = obj.ref().j;
        // :: error: assignment.type.incompatible
        a = StaticTest.j;
    }
}
