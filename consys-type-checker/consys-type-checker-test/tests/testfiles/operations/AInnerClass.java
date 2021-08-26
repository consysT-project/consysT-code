package testfiles.operations;

import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;

public @Mixed class AInnerClass {
    private @Strong int i;

    public class Inner {
        void test() {
            i = 0;
        }
    }
}
