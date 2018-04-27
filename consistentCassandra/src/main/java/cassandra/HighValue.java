package cassandra;

import com.datastax.driver.core.ConsistencyLevel;
import com.datastax.driver.core.ResultSet;
import com.datastax.driver.core.Session;
import com.datastax.driver.core.Statement;
import com.github.allprojects.consistencyTypes.qual.High;

import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Supplier;

public class HighValue<@High T> extends ExecutableWrapper<T> {

    public HighValue(T wrappedObject, Session session,
                     Supplier<T> read,
                     Consumer<T> write,
                     Wrappable parent) {
        super(wrappedObject, session, read, write, parent);
    }

    T value(Scope scope) {
        @SuppressWarnings("consistency")
        T value = read();
        return value;
    }

    public <V> V perform(Function<T, V> function) {
        return function.apply(read());
    }

    @High
    @SuppressWarnings("consistency")
    public ResultSet execute(@High Statement statement) {
        statement.setConsistencyLevel(ConsistencyLevel.ALL);
        @SuppressWarnings("consistency")
        @High ResultSet result = getSession().execute(statement);
        return result;
    }
}
