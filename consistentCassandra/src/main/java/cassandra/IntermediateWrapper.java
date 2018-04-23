package cassandra;

import java.util.HashSet;
import java.util.Set;

public class IntermediateWrapper<T extends Wrappable> extends AbstractConsistencyWrapper<T> {

    Set<AbstractConsistencyWrapper> wrappers;

    public IntermediateWrapper(T wrappedObject) {
        super(wrappedObject);
        wrappers = new HashSet<>();
    }

    public boolean addWrapper(AbstractConsistencyWrapper w){
        return wrappers.add(w);
    }

    @Override
    void write() {
        wrappers.forEach(w -> w.write());
    }

    @Override
    T read() {
        wrappers.forEach(w -> w.read());
        return getWrappedObject();
    }

    @Override
    public T value() {
        return read();
    }
}
