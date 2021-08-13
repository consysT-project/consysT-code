package testfiles.operations;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.Ref;

public class StaticTest {
    static @Mixed class A {
        static int i;
    }

    @Transactional
    void test(Ref<@Mixed A> obj) {
        // :: error: assignment.type.inconsistent
        @Weak int a = obj.ref().i;
    }
}
