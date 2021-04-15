package de.tuda.stg.consys.checker.testfiles.legacy;


import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;

public class ReceiverRestriction {

    @Weak ReceiverRestriction highTestObject = new @Weak ReceiverRestriction();
    @Strong ReceiverRestriction lowTestObject = new @Strong ReceiverRestriction();


    void onlyForHigh(@Weak ReceiverRestriction this){

    }

    void onlyForLow(@Strong ReceiverRestriction this){

    }

    void testMethodInvocation(){
        highTestObject.onlyForHigh();
        highTestObject.onlyForLow();

        // :: error: (method.invocation.invalid)
        lowTestObject.onlyForHigh();
        lowTestObject.onlyForLow();
    }
}
