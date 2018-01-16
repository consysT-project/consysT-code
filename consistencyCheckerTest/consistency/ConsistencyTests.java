import com.github.allprojects.consistencyTypes.qual.*;

class ConsistencyTests {

    void lowToHigh() {
        @High int a;
        @Low int b = 42;
        // :: error: (assignment.type.incompatible)
        a = b;
    }

    void highToLow() {
        @Low int a;
        @High int b = 42;
        a = b;
    }

    void unannotated() {
        @Low int a;
        @High int b;
        int c = 42;
        a = c;
        // :: error: (assignment.type.incompatible)
        b = c;
    }

    void literalAssignment() {
        @Low int a = 42;
        @High int b = 42;

        @Low String c = "Don't panic!";
        @High String d = "Don't panic!";
    }

    void wantsHigh(@High int a) { }
    void wantsLow(@Low int a) { }
    void wantsAnything(int a) { }

    void methodArguments() {
        @High int high = 42;
        @Low int low = 21;

        wantsHigh(high);
        // :: error: (argument.type.incompatible)
        wantsHigh(low);

        wantsLow(high);
        wantsLow(low);

        wantsAnything(high);
        wantsAnything(low);
    }

    @Low int getLow() { return 42; }
    @High int getHigh() { return 42; }
    int getAnything() { return 42; }

    void methodAnnotation() {
        @Low int low = getLow();
        low = getHigh();
        low = getAnything();

        @High int high = getHigh();
        // :: error: (assignment.type.incompatible)
        high = getLow();
        // :: error: (assignment.type.incompatible)
        high = getAnything();
    }

    @Low int lowMethodLowReturn() { @Low int low = 42; return low; }
    @Low int lowMethodHighReturn() { @High int high = 42; return high; }

    // :: error: (return.type.incompatible)
    @High int highMethodLowReturn() { @Low int low = 42; return low; }
    @High int highMethodHighReturn() { @High int high = 42; return high; }

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

    @High int sanitize(int anything) {
        @SuppressWarnings("consistency")
        @High int sanitized = anything;
        return sanitized;
    }

    void testSanitize() {
        @Low int low = 42;
        @High int high = sanitize(low);
    }

}
