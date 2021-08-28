import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Mutable;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.Ref;

import java.io.Serializable;

public class ZReturnTypeTest {
    @Transactional
    void test(Ref<@Mutable ReturnTypeTest_Class> o) {
        @Strong int a;
        a = o.ref().f();

        // :: error: assignment.type.incompatible
        a = o.ref().g(true);
        @Weak int b;
        b = o.ref().g(true);

        // :: error: assignment.type.incompatible
        b = o.ref().h2();
    }
}

abstract @Mixed class ReturnTypeTest_Class {
    static class Box { int value; }

    private int i;
    private @Weak int j;
    private @Weak Box wb;
    private @Strong Box sb;

    @StrongOp
    int f() {
        i = 0;
        return i;
    }

    int g(boolean b) {
        if (b)
            return i;
        else
            return j;
    }

    Box b(boolean t) { // standard is Immutable, subtyping allowed, inference works
        if (t) return wb;
        else return sb;
    }

    @Mutable Box b1(boolean t) { // inference runs, but subtyping not allowed -> error
        if (t) return wb;
            // :: error: return.type.incompatible
        else return sb;
    }

    void h() { }
    abstract void h1();
    abstract int h2(); // this stays Inconsistent
}
