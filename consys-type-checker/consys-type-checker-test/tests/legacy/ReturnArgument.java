package de.tuda.stg.consys.checker.testfiles.legacy;

import de.tuda.stg.consys.checker.qual.PolyConsistent;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;

class ReturnArgument {

    @PolyConsistent int identity(@PolyConsistent int number) {return number; }

    void returnArgument() {
        @Weak int high = 42;
        @Strong int low = 42;

        @Weak int a = identity(high);
        // :: error: (assignment.type.incompatible)
        a = identity(low);

        @Strong int b = identity(high);
        b = identity(low);
    }
}