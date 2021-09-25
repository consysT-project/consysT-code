import de.tuda.stg.consys.annotations.methods.*;
import de.tuda.stg.consys.checker.qual.*;

import java.util.LinkedList;

/**
 * Tests usage of an inherited field with an incompatible operation level,
 * where the Base class is not part of the project package.
 */
public @Mixed(StrongOp.class) class ThirdPartyTest extends LinkedList<String> {
    @WeakOp
    void write() {
        // :: warning: mixed.inheritance.field.overwrite
        super.modCount = 0;
    }
}