import com.github.allprojects.consistencyTypes.qual.*;

public class Test {

    @Low private int getLowValue(){
        return 1;
    }

    @High private int getHighValue(){
        return 1;
    }

    void shouldFail() {
        @High int a = getHighValue();
        int b = getLowValue();
        @High int c = a + b;
    }
}