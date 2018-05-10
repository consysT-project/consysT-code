package com.github.allprojects.consistencyTypes.cassandraInterface;

import java.util.HashSet;
import java.util.Set;

/**
 * Scope is used to prevent infinite updates with wrappers, that are in cyclic dependency.
 */
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
