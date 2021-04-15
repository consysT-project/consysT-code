package de.tuda.stg.consys.checker.testfiles.legacy;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;

class MethodArguments {
    void wantsHigh(@Weak int a) { }
    void wantsLow(@Strong int a) { }
    void wantsAnything(int a) { }

    void methodArguments() {
        @Weak int high = 42;
        @Strong int low = 21;

        wantsHigh(high);
        // :: error: (argument.type.incompatible)
        wantsHigh(low);

        wantsLow(high);
        wantsLow(low);

        wantsAnything(high);
        wantsAnything(low);
    }
}
