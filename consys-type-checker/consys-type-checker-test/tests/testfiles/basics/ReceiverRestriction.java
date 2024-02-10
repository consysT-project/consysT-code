package de.tuda.stg.consys.checker.testfiles.legacy;

import de.tuda.stg.consys.annotations.*;
import de.tuda.stg.consys.checker.qual.*;

//@skip-test
public class ReceiverRestriction {

    @Weak ReceiverRestriction weakTestObject = new ReceiverRestriction();
    @Strong ReceiverRestriction strongTestObject = new ReceiverRestriction();

    void onlyForWeak(@Weak ReceiverRestriction this) { }

    void onlyForStrong(@Strong ReceiverRestriction this) { }


    @Transactional
    void testMethodInvocation(){
        weakTestObject.onlyForWeak();
        weakTestObject.onlyForStrong();

        // :: error: (method.invocation.invalid)
        strongTestObject.onlyForWeak();
        strongTestObject.onlyForStrong();
    }
}
