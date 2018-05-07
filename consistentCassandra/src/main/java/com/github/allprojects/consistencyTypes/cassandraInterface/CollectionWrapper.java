package com.github.allprojects.consistencyTypes.cassandraInterface;

import java.util.Collection;

public class CollectionWrapper<T extends Collection<Wrappable>> extends ConsistencyWrapper<T> {

    private T collection;

    public CollectionWrapper(T collection) {
        super(collection);
        this.collection = collection;
    }

    @Override
    public T value(Scope scope) {
        collection.forEach(w -> w.getWrapper().value(scope));
        return getWrappedObject();
    }

    public boolean add(Wrappable object){
        return collection.add(object);
    }
}
