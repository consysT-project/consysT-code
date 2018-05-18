import com.github.allprojects.consistencyTypes.qual.High;
import com.github.allprojects.consistencyTypes.qual.Low;

public class ReceiverRestriction {

    @High ReceiverRestriction highTestObject = new @High ReceiverRestriction();
    @Low ReceiverRestriction lowTestObject = new @Low ReceiverRestriction();


    void onlyForHigh(@High ReceiverRestriction this){

    }

    void onlyForLow(@Low ReceiverRestriction this){

    }

    void testMethodInvocation(){
        highTestObject.onlyForHigh();
        highTestObject.onlyForLow();

        // :: error: (method.invocation.invalid)
        lowTestObject.onlyForHigh();
        lowTestObject.onlyForLow();
    }
}
