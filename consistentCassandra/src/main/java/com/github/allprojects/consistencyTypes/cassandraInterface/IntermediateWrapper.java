package com.github.allprojects.consistencyTypes.cassandraInterface;

import java.util.HashSet;
import java.util.Set;

public class IntermediateWrapper<T extends Wrappable> extends ConsistencyWrapper<T> {

    Set<ConsistencyWrapper> wrappers;

    public IntermediateWrapper(T wrappedObject) {
        super(wrappedObject);
        wrappers = new HashSet<>();
    }

    public boolean addWrapper(ConsistencyWrapper w){
        return wrappers.add(w);
    }

    @Override
    public T value(Scope scope) {
        wrappers.forEach(w -> scope.read(w));
        return getWrappedObject();
    }
}
