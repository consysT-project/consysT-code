package de.tuda.stg.consys.checker.testfiles.legacy;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;

class LiteralAssignment {
    void literalAssignment() {
        @Strong int a = 42;
        @Weak int b = 42;

        @Strong String c = "Don't panic!";
        @Weak String d = "Don't panic!";
    }
}