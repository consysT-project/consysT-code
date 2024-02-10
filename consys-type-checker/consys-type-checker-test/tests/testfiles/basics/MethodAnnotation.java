package de.tuda.stg.consys.checker.testfiles.legacy;

import de.tuda.stg.consys.annotations.*;
import de.tuda.stg.consys.checker.qual.*;

class MethodAnnotation {

    @Strong int getStrong() { return 42; }
    @Weak int getWeak() { return 42; }
    int getInconsistent() { return 42; }

    @Transactional
    void methodAnnotation() {
        @Strong int s = getStrong();
        // :: error: (assignment)
        s = getWeak();
        // :: error: (assignment)
        s = getInconsistent();

        @Weak int w = getWeak();
        w = getStrong();
        // :: error: (assignment)
        w = getInconsistent();
    }

    @Strong int strongMethodStrongReturn() { @Strong int s = 42; return s; }
    // :: error: (return)
    @Strong int strongMethodWeakReturn() { @Weak int w = 42; return w; }

    @Weak int weakMethodStrongReturn() { @Strong int s = 42; return s; }
    @Weak int weakmethodWeakReturn() { @Weak int w = 42; return w; }
}
