import de.tuda.stg.consys.annotations.Transactional;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Local;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.japi.Ref;

// TODO: nested classes expose private fields to enclosing class

public class PublicTest {
    @Transactional
    void test(Ref<@Mixed(withDefault = WeakOp.class) A> objW,
              Ref<@Mixed(withDefault = StrongOp.class) A> objS) {
        // :: error: assignment.type.incompatible
        @Strong int a = objW.ref().a;
        @Weak int a1 = objW.ref().a;
        // :: error: assignment.type.incompatible
        @Strong int b = objW.ref().b;
        @Weak int b1 = objW.ref().b;

        // :: error: assignment.type.incompatible
        @Local int c = objS.ref().a;
        @Strong int c1 = objS.ref().a;
        // :: error: assignment.type.incompatible
        @Local int d = objS.ref().b;
        @Strong int d1 = objS.ref().b;

        // :: error: assignment.type.incompatible
        @Strong int e = objW.ref().a1;
        @Weak int e1 = objW.ref().a1;
        // :: error: assignment.type.incompatible
        @Strong int f = objW.ref().b1;
        @Weak int f1 = objW.ref().b1;
    }
}

class A {
    public int a;
    public int a1;
    int b;
    int b1;

    @WeakOp
    void f() {
        a1 = 0;
        b1 = 0;
    }
}
