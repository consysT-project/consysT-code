import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.Ref;

public @Mixed class StaticTest {
    // :: error: mixed.field.static.incompatible
    static @Weak int i;
    static int j;

    @Transactional
    void test(Ref<@Mixed StaticTest> obj) {
        @Weak int a;
        // :: error: assignment
        a = obj.ref().i;
        // :: error: assignment
        a = StaticTest.i;
        // :: error: assignment
        a = obj.ref().j;
        // :: error: assignment
        a = StaticTest.j;
    }
}
