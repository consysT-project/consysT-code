import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.Ref;

public class AStaticTest {
    // :: error: mixed.field.static.incompatible
    static @Weak int i;
    static int j;

    @Transactional
    void test(Ref<@Mixed AStaticTest> obj) {
        @Weak int a;
        // :: error: assignment.type.incompatible
        a = obj.ref().i;
        // :: error: assignment.type.incompatible
        a = AStaticTest.i;
        // :: error: assignment.type.incompatible
        a = obj.ref().j;
        // :: error: assignment.type.incompatible
        a = AStaticTest.j;
    }
}
