package operations;

import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;

public class ReadOnlyTest {
    static @Mixed class A {
        @Strong int i;
        @Weak int j;

        int f() {
            return i;
        }
    }
}
