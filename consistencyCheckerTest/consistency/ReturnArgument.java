import com.github.allprojects.consistencyTypes.qual.*;

class ReturnArgument {

    int returnPassedLow(@Low int low) { return low; }
    int returnPassedHigh(@High int high) { return high; }
    int returnPassedAnything(int anything) { return anything; }

    void valueThroughMethod() {
        @High int high = 42;
        @Low int low = 42;

        @High int a = returnPassedHigh(high);
        a = returnPassedAnything(high);
        // :: error: (assignment.type.incompatible)
        a = returnPassedAnything(low);
        // :: error: (assignment.type.incompatible)
        a = returnPassedLow(low);

        @Low int b = returnPassedHigh(high);
        b = returnPassedAnything(high);
        b = returnPassedAnything(low);
        b = returnPassedLow(low);
    }

}
