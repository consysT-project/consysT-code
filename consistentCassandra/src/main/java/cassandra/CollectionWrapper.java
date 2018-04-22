package cassandra;

import java.util.Collection;

public class CollectionWrapper<T extends Collection<Wrappable>> extends AbstractConsistencyWrapper<T>{

    private T wrapper;

    public CollectionWrapper(T wrappedObject) {
        super(wrappedObject);
        wrapper = wrappedObject;
    }

    @Override
    void write() {
        wrapper.forEach(w -> w.getWrapper().write());
    }

    @Override
    T read() {
        wrapper.forEach(w -> w.getWrapper().read());
        return getWrappedObject();
    }

    @Override
    public T value() {
        return getWrappedObject();
    }

    public boolean add(Wrappable object){
        object.getWrapper().write();
        return wrapper.add(object);
    }
}
