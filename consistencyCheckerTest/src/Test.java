import com.github.allprojects.consistencyTypes.qual.*;

public class Test {

    void shouldFail() {
        @High int h1 = 0;
        @High int h2 = 1;
        @Low int l1 = 0;
        l1 = h1;
        h2 = l1;
    }
}