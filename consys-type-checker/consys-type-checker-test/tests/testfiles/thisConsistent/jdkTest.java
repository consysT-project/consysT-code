package de.tuda.stg.consys.checker.testfiles.tmp;

import de.tuda.stg.consys.checker.qual.Strong;

public class jdkTest {
    public void test(@Strong Number n) {
        @Strong float f = n.floatValue();
    }
}