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

    void literalAssignment() {
        @Low int a = 42;
        @High int b = 42;

        @Low String c = "Don't panic!";
        @High String d = "Don't panic!";
    }

    void wantsHigh(@High int a) { }
    void wantsLow(@Low int a) { }

    void methodArguments() {
        @High int high = 42;
        @Low int low = 21;

        wantsHigh(high);
        // :: error: (argument.type.incompatible)
        wantsHigh(low);

        wantsLow(high);
        wantsLow(low);
    }

}
