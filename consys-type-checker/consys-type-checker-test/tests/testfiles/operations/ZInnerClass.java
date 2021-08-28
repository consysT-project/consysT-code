package testfiles.operations;

import de.tuda.stg.consys.checker.qual.Mixed;
import de.tuda.stg.consys.checker.qual.Strong;

public @Mixed class ZInnerClass {
    private @Strong int i;

    public class Inner {
        void test() {
            i = 0;
        }
    }
}
