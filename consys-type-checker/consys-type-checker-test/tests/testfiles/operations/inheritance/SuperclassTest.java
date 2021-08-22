package testfiles.operations.inheritance;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Weak;

public class SuperclassTest { }

@Mixed(StrongOp.class) class SuperclassTestDerivedA extends SuperclassTestBaseA {
    // since the base class methods are now @StrongOp, there is an error at setI()
}

class SuperclassTestBaseA {
    private int i;

    // TODO: better error message, i.e. info about which derived class leads to error
    void setI(@Weak int j) {
        // :: error: assignment.type.incompatible
        i = j;
    }
}

class SuperclassTestBaseB {
    private int i;

    // TODO: better error message, i.e. info about which derived class leads to error
    void setI(@Weak int j) {
        // :: error: assignment.type.incompatible
        i = j;
    }
}

@Mixed(StrongOp.class) class SuperclassTestDerivedB extends SuperclassTestBaseB {
    // since the base class methods are now @StrongOp, there is an error at setI()
}
