package de.tuda.stg.consys.checker.testfiles.tmp;

import de.tuda.stg.consys.checker.qual.*;

public class AjdkTest {
    public void test(@Strong Number n, @Weak Number x) {
        @Strong float f1 = n.floatValue();
        // :: error: assignment
        @Local float f2 = n.floatValue();
        @Weak float f3 = n.floatValue();

        @Weak float f4 = x.floatValue();
        // :: error: assignment
        @Strong float f5 = x.floatValue();
        @Inconsistent float f6 = x.floatValue();
    }
}