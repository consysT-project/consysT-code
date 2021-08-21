

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;

import java.io.Serializable;

public class InheritanceTest {
}

@Mixed class Base implements Serializable {
    protected int k; // inferred weak
    protected int h; // inferred strong

    @WeakOp
    void setK() { k = 0; }

    @StrongOp
    void setH(@Strong int i) {
        h = i;
    }
}

@Mixed class Derived extends Base {
    private int j; // inferred strong

    @WeakOp
    void setHDerived() {
        // :: error: mixed.inheritance.field.overwrite
        h = 0;
    }

    @StrongOp
    void setJfromK() {
        // :: error: assignment.type.incompatible
        j = k;
    }

    @StrongOp
    void setJfromH() {
        // h is still strong, but an error is thrown in setHDerived
        j = h;
    }
}
