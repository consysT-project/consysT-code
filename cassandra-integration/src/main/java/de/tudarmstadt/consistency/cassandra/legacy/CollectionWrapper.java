package de.tudarmstadt.consistency.cassandra.legacy;

import java.util.Collection;

/**
 * Wrapper for collections of Wrappables, allows batch updating.
 * @param <T> Type of the collection, which must be parameterized with ConsistencyObject.
 */
public class CollectionWrapper<T extends Collection<ConsistencyObject>> extends ConsistencyWrapper<T> {

    private T collection;

    public CollectionWrapper(T collection) {
        super(collection);
        this.collection = collection;
    }

    @Override
    T value(Scope scope) {
        collection.forEach(w -> w.getWrapper().value(scope));
        return getWrappedObject();
    }

    public boolean add(ConsistencyObject object) {
        return collection.add(object);
    }
}
