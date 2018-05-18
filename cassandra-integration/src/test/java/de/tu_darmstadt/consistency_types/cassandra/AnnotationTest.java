package de.tu_darmstadt.consistency_types.cassandra;

import de.tu_darmstadt.consistency_types.cassandra.ConsistencyObject;
import de.tu_darmstadt.consistency_types.cassandra.HighValue;
import de.tu_darmstadt.consistency_types.cassandra.LowValue;
import de.tu_darmstadt.consistency_types.checker.qual.High;

public class AnnotationTest {

    class A extends ConsistencyObject {
        HighValue<@High Integer> highWrapper = new HighValue<>(0, null, null, null, null);
        LowValue<Integer> lowWrapper = new LowValue<>(0, null, null, null, null);

        private void test() {
            @High Integer highValue = highWrapper.value();
            // shouldFail
            highValue = lowWrapper.value();
            Integer lowValue = lowWrapper.value();
            lowValue = highWrapper.value();

            highWrapper.setValue(highValue);
            // should fail
            highWrapper.setValue(lowValue);
            lowWrapper.setValue(highValue);
            lowWrapper.setValue(lowValue);

        }
    }

}
