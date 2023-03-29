package de.tuda.stg.consys.checker.testfiles.legacy;

import de.tuda.stg.consys.annotations.*;
import de.tuda.stg.consys.checker.qual.*;

class MethodArguments {
    void wantsWeak(@Weak int a) { }
    void wantsStrong(@Strong int a) { }
    void wantsAnything(int a) { }

    @Transactional
    void methodArguments() {
        @Weak int w = 42;
        @Strong int s = 21;

        wantsWeak(w);
        wantsWeak(s);

        // :: error: (argument)
        wantsStrong(w);
        wantsStrong(s);

        wantsAnything(w);
        wantsAnything(s);
    }
}
