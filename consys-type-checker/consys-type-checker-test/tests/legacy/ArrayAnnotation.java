package de.tuda.stg.consys.checker.testfiles.legacy;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;

public class ArrayAnnotation {

    @Weak int[] higharr = {1,2,3};
    @Strong int[] lowarr = {1,2,3};

    @Weak int a = 1;
    @Strong int b = 2;
    @Weak int c = 3;

    // :: error: (array.initializer.type.incompatible) :: error: (assignment.type.incompatible)
    @Weak int[] highmixed = {a,b,c};
    @Strong int[] lowmixed = {a,b,c};

    int[] mixed = {a,b,c};

    void testIterating() {
        @Weak int high;
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
        for (@Weak int i: higharr) {
            high = i;
        }
        // :: error: (enhancedfor.type.incompatible)
        for (@Weak int i: lowmixed) { }
    }

    void testArrayAssignment(){
        // :: error: (assignment.type.incompatible)
        higharr[0] = b;
        higharr[0] = a;
    }
}