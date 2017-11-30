import com.github.allprojects.consistencyTypes.qual.*;

public class Test {

    void shouldFail() {
        @High int a = 0;
        @Low int b = 1;
        @High int c = a + b;
    }

}