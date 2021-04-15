package de.tuda.stg.consys.checker.testfiles.legacy;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;

class Sanitizing {

    @Weak int sanitize(int anything) {
        @SuppressWarnings("consistency")
        @Weak int sanitized = anything;
        return sanitized;
    }

    void testSanitize() {
        @Strong int low = 42;
        @Weak int high = sanitize(low);
    }

}
