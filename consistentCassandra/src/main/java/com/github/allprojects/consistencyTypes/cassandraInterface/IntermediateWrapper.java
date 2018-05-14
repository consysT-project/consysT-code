package com.github.allprojects.consistencyTypes.cassandraInterface;

import java.util.HashSet;
import java.util.Set;

/**
 * Wrapper for objects that are not directly related to some database content,
 * but instead are composed from members that are wrapped themselves by a ConsistencyWrapper
 */
public class IntermediateWrapper<T extends Wrappable> extends ConsistencyWrapper<T> {

    Set<ConsistencyWrapper> wrappers;

    public IntermediateWrapper(T wrappedObject) {
        super(wrappedObject);
        wrappers = new HashSet<>();
    }

    boolean addWrapper(ConsistencyWrapper w){
        return wrappers.add(w);
    }

    @Override
    T value(Scope scope) {
        wrappers.forEach(scope::read);
        return getWrappedObject();
    }
}
