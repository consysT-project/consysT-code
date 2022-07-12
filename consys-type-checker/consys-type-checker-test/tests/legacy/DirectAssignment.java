package de.tuda.stg.consys.checker.testfiles.legacy;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;

class DirectAssignment {
    void lowToHigh() {
        @Weak int a;
        @Strong int b = 42;
        // :: error: (assignment.type.incompatible)
        a = b;
    }

    void highToLow() {
        @Strong int a;
        @Weak int b = 42;
        a = b;
    }

    void unannotated() {
        @Strong int a;
        @Weak int b;
        int c = 42;
        a = c;
        // :: error: (assignment.type.incompatible)
        b = c;
    }

    void annotatedInstances(){
        @Strong DirectAssignment low = new @Weak DirectAssignment();
        @Weak DirectAssignment high = new @Weak DirectAssignment();

        low = new @Strong DirectAssignment();
        // :: error: (assignment.type.incompatible)
        high = new @Strong DirectAssignment();
    }
}