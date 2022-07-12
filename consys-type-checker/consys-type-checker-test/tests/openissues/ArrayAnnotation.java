package de.tuda.stg.consys.checker.testfiles.openissues;

import de.tuda.stg.consys.checker.qual.*;

public class ArrayAnnotation {

    @Strong int[] higharr = {1,2,3};
    @Weak int[] lowarr = {1,2,3};

    @Strong int a = 1;
    @Weak int b = 2;
    @Strong int c = 3;

    // :: error: (array.initializer.type.incompatible) :: error: (assignment.type.incompatible)
    @Strong int[] highmixed = {a,b,c};
    @Weak int[] lowmixed = {a,b,c};

    int[] mixed = {a,b,c};

    void testIterating() {
        @Strong int high;
        for (int i: mixed) {
            // :: error: (assignment.type.incompatible)
            high = i;
        }
        /**
         * an assignment to the iterator i is possible. Therefore i must be annotated @Strong to be able to assign i to a @Strong variable.
         */
        for (int i: higharr) {
            // :: error: (assignment.type.incompatible)
            high = i;
        }
        for (@Strong int i: higharr) {
            high = i;
        }
        // :: error: (enhancedfor.type.incompatible)
        for (@Strong int i: lowmixed) { }
    }

    void testArrayAssignment(){
        // :: error: (assignment.type.incompatible)
        higharr[0] = b;
        higharr[0] = a;
    }
}