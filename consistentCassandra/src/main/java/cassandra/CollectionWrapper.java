package cassandra;

import java.util.Collection;

public class CollectionWrapper<T extends Collection<Wrappable>> extends AbstractConsistencyWrapper<T>{

    private T collection;

    public CollectionWrapper(T collection) {
        super(collection);
        collection = collection;
    }

    @Override
    void write(Scope scope) {
        collection.forEach(w -> scope.write(w.getWrapper()));
    }

    @Override
    T read(Scope scope) {
        collection.forEach(w -> scope.read(w.getWrapper()));
        return getWrappedObject();
    }

    @Override
    public T value() {
        return read(new Scope());
    }

    @Override
    public void setValue(T collection) {

    }

    public boolean add(Wrappable object){
        object.getWrapper().write(new Scope());
        return collection.add(object);
    }
}
