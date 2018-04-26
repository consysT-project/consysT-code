package cassandra;

import com.datastax.driver.core.ConsistencyLevel;
import com.datastax.driver.core.ResultSet;
import com.datastax.driver.core.Session;
import com.datastax.driver.core.Statement;
import com.github.allprojects.consistencyTypes.qual.High;

import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Supplier;

public class HighValue<@High T> extends AbstractExecutableWrapper<T> {

    public HighValue(T wrappedObject, Session session,
                     Supplier<T> read,
                     Consumer<T> write,
                     Wrappable parent) {
        super(wrappedObject, session, read, write, parent);
    }

    public T value() {
        @SuppressWarnings("consistency")
        T value = read(new Scope());
        return value;
    }

    public <V> V perform(Function<T, V> function) {
        return function.apply(read(new Scope()));
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
