package testfiles.operations;

import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.japi.Ref;

public class AAAAReturnTest {
    private int i;
    private @Strong int j;
    @StrongOp private void write() { i = 0; }

    @StrongOp public int get() {
        return i;
    }

    @Transactional static void test(Ref<@Mutable @Mixed AAAAReturnTest> obj) {
        @Strong int a = obj.ref().get();
    }
}
