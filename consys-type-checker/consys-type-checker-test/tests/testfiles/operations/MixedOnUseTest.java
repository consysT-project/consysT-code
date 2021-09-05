package testfiles.operations;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Local;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.Ref;
// TODO: try a few more types if it fails
public class MixedOnUseTest {
    static class A {
        int i;

        void f() {
            i = 0;
        }
    }

    void testRefAssignment(Ref<@Mixed(WeakOp.class) A> mixedWeak,
              Ref<@Mixed(StrongOp.class) A> mixedStrong,
              Ref<@Weak A> weak, Ref<@Strong A> strong) {

        weak = mixedWeak;
        weak = mixedStrong;
        weak = strong;

        // :: error: assignment.type.incompatible
        strong = weak;
        // :: error: assignment.type.incompatible
        strong = mixedStrong;
        // :: error: assignment.type.incompatible
        strong = mixedWeak;
    }

    @Transactional
    void testFields(Ref<@Mixed(WeakOp.class) A> mixedWeak,
                           Ref<@Mixed(StrongOp.class) A> mixedStrong,
                           Ref<@Weak A> weak, Ref<@Strong A> strong) {

        // :: error: assignment.type.incompatible
        @Local int a = mixedStrong.ref().i;
        // :: error: assignment.type.incompatible
        a = strong.ref().i;
        @Strong int b = mixedStrong.ref().i;
        b = strong.ref().i;

        // :: error: assignment.type.incompatible
        @Strong int c = mixedWeak.ref().i;
        // :: error: assignment.type.incompatible
        c = weak.ref().i;
        @Weak int d = mixedWeak.ref().i;
        d = weak.ref().i;
    }
}
