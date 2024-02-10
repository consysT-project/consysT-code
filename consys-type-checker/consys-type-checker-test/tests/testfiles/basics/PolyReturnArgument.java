package de.tuda.stg.consys.checker.testfiles.legacy;

import de.tuda.stg.consys.annotations.*;
import de.tuda.stg.consys.checker.qual.*;

class PolyReturnArgument {

    @PolyConsistent int identity(@PolyConsistent int number) { return number; }

    @Transactional
    void returnArgument() {
        @Weak int w = 42;
        @Strong int s = 42;

        @Weak int a = identity(w);
        a = identity(s);

        // :: error: (assignment)
        @Strong int b = identity(w);
        b = identity(s);
    }
}