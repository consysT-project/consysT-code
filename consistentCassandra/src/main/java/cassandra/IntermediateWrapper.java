package cassandra;

import java.util.HashSet;
import java.util.Set;

public class IntermediateWrapper<T extends Wrappable> extends AbstractConsistencyWrapper<T> {

    Set<AbstractConsistencyWrapper> wrapper;

    public IntermediateWrapper(T wrappedObject) {
        super(wrappedObject);
        wrapper = new HashSet<>();
    }

    public boolean addWrapper(AbstractConsistencyWrapper w){
        return wrapper.add(w);
    }

    @Override
    void write() {
        wrapper.forEach(w -> w.write());
    }

    @Override
    T read() {
        wrapper.forEach(w -> w.read());
        return getWrappedObject();
    }

    @Override
    public T value() {
        return getWrappedObject();
    }
}
