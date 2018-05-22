package de.tu_darmstadt.consistency_types.cassandra;

import de.tu_darmstadt.consistency_types.checker.qual.Strong;

public class AnnotationTest {

    class A extends ConsistencyObject {
        HighValue<@Strong Integer> highWrapper = new HighValue<>(0, null, null, null, null);
        LowValue<Integer> lowWrapper = new LowValue<>(0, null, null, null, null);

        private void test() {
            @Strong Integer highValue = highWrapper.value();
            // shouldFail
          //  highValue = lowWrapper.value();
            Integer lowValue = lowWrapper.value();
            lowValue = highWrapper.value();

            highWrapper.setValue(highValue);
            // should fail
           // highWrapper.setValue(lowValue);
            lowWrapper.setValue(highValue);
            lowWrapper.setValue(lowValue);

        }
    }

}
