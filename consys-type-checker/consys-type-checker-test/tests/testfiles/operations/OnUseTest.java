import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.Ref;

/**
 * Tests that errors are reported for class consistency usages in the program.
 */
// :: error: consistency.type.use.incompatible
public class OnUseTest {
    private int i;
    void set(@Weak int i) {
        this.i = i; // error produced by Strong and Mixed(StrongOp) instances
    }

    static class Test {
        @Transactional static void test(Ref<@Weak OnUseTest> weak,
                                        Ref<@Strong OnUseTest> strong,
                                        Ref<@Mixed(WeakOp.class) OnUseTest> mixedWeak,
                                        Ref<@Mixed(StrongOp.class) OnUseTest> mixedStrong) {}
    }
}
