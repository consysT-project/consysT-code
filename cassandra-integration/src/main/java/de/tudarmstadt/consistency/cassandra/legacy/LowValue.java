package de.tudarmstadt.consistency.cassandra.legacy;

import com.datastax.driver.core.ConsistencyLevel;
import com.datastax.driver.core.Session;

import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Supplier;

public class LowValue<T> extends ExecutableWrapper<T> {

    private int accessCount = 0;

    public LowValue(T wrappedObject, Session session,
                    Supplier<T> read,
                    Consumer<T> write,
                    ConsistencyObject parent) {
        super(wrappedObject, session, read, write, parent);
    }

    T value(Scope scope) {
        if (++accessCount % 5 == 0) {
            read();
            accessCount = 0;
        }
        return getWrappedObject();
    }

    public ConsistencyLevel getConsistencyLevel() {
        return ConsistencyLevel.ONE;
    }

    public <V> V perform(Function<T, V> function) {
        return function.apply(read());
    }
}
