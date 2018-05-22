import com.github.allprojects.consistencyTypes.qual.High;
import com.github.allprojects.consistencyTypes.qual.Low;

public class ArrayAnnotation {

    @High int[] higharr = {1,2,3};
    @Low int[] lowarr = {1,2,3};

    @High int a = 1;
    @Low int b = 2;
    @High int c = 3;

    // :: error: (array.initializer.type.incompatible) :: error: (assignment.type.incompatible)
    @High int[] highmixed = {a,b,c};
    @Low int[] lowmixed = {a,b,c};

    int[] mixed = {a,b,c};

    void testIterating() {
        @High int high;
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
        for (@High int i: higharr) {
            high = i;
        }
        // :: error: (enhancedfor.type.incompatible)
        for (@High int i: lowmixed) { }
    }

    void testArrayAssignment(){
        // :: error: (assignment.type.incompatible)
        higharr[0] = b;
        higharr[0] = a;
    }
}