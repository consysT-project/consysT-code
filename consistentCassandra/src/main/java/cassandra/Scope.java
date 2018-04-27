package cassandra;

import java.util.HashSet;
import java.util.Set;

class Scope {

    private Set<ConsistencyWrapper> processed = new HashSet<>();

    void write(ConsistencyWrapper wrapper) {
        if (processed.add(wrapper)) {
            wrapper.setValue(wrapper.getWrappedObject(), this);
        }
    }

    void read(ConsistencyWrapper wrapper) {
        if (processed.add(wrapper)) {
            wrapper.value(this);
        }
    }
}
