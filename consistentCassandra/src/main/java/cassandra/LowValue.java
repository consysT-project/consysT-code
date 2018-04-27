package cassandra;

import com.datastax.driver.core.ConsistencyLevel;
import com.datastax.driver.core.ResultSet;
import com.datastax.driver.core.Session;
import com.datastax.driver.core.Statement;
import com.github.allprojects.consistencyTypes.qual.Low;

import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Supplier;

public class LowValue<@Low T> extends ExecutableWrapper<T> {

    private int accessCount = 0;

    public LowValue(T wrappedObject, Session session,
                    Supplier<T> read,
                    Consumer<T> write,
                    Wrappable parent) {
        super(wrappedObject, session, read, write, parent);
    }

    T value(Scope scope) {
        if (++accessCount % 5 == 0) {
            read();
            accessCount = 0;
        }
        return getWrappedObject();
    }

    public <V> V perform(Function<T, V> function) {
        return function.apply(read());
    }

    @Low public ResultSet execute(Statement statement) {
        statement.setConsistencyLevel(ConsistencyLevel.ONE);
        return getSession().execute(statement);
    }
}
