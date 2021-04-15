package de.tuda.stg.consys.checker.testfiles.legacy;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;

class MethodAnnotation {

    @Strong int getLow() { return 42; }
    @Weak int getHigh() { return 42; }
    int getAnything() { return 42; }

    void methodAnnotation() {
        @Strong int low = getLow();
        low = getHigh();
        low = getAnything();

        @Weak int high = getHigh();
        // :: error: (assignment.type.incompatible)
        high = getLow();
        // :: error: (assignment.type.incompatible)
        high = getAnything();
    }

    @Strong int lowMethodLowReturn() { @Strong int low = 42; return low; }
    @Strong int lowMethodHighReturn() { @Weak int high = 42; return high; }

    // :: error: (return.type.incompatible)
    @Weak int highMethodLowReturn() { @Strong int low = 42; return low; }
    @Weak int highMethodHighReturn() { @Weak int high = 42; return high; }

}
