import com.github.allprojects.consistencyTypes.qual.*;

class LiteralAssignment {
    void literalAssignment() {
        @Low int a = 42;
        @High int b = 42;

        @Low String c = "Don't panic!";
        @High String d = "Don't panic!";
    }
}