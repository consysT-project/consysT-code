package de.tudarmstadt.consistency.cassandra.legacy;

import com.datastax.driver.core.ConsistencyLevel;
import com.datastax.driver.core.Session;
import de.tudarmstadt.consistency.checker.qual.Strong;

import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Supplier;

public class HighValue<T extends @Strong Object> extends ExecutableWrapper<T> {

    public HighValue(T wrappedObject, Session session,
                     Supplier<T> read,
                     Consumer<T> write,
                     ConsistencyObject parent) {
        super(wrappedObject, session, read, write, parent);
    }

    T value(Scope scope) {
        return read();
    }

    public ConsistencyLevel getConsistencyLevel() {
        return ConsistencyLevel.ALL;
    }

    public <V> V perform(Function<T, V> function) {
        return function.apply(read());
    }
}
