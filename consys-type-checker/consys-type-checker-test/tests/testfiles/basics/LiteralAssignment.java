package de.tuda.stg.consys.checker.testfiles.legacy;

import de.tuda.stg.consys.annotations.*;
import de.tuda.stg.consys.checker.qual.*;

class LiteralAssignment {
    static class A {}

    // literals are Local by default
    @Transactional
    void literalAssignment() {
        @Strong int a = 42;
        @Weak int b = 42;

        @Strong String c = "Don't panic!";
        @Weak String d = "Don't panic!";

        @Strong A e = new A();
        @Weak A f = new A();
    }
}