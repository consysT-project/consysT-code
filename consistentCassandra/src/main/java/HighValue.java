import com.datastax.driver.core.ConsistencyLevel;
import com.datastax.driver.core.ResultSet;
import com.datastax.driver.core.Statement;
import com.github.allprojects.consistencyTypes.qual.High;

import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Supplier;

public class HighValue<@High T> extends AbstractConsistencyWrapper<T> {

    public HighValue(T wrappedObject, ConsistentCassandraConnector connector,
                     Supplier<T> read,
                     Consumer<T> write) {
        super(wrappedObject, connector, read, write);
    }

    @High public T value() {
        @SuppressWarnings("consistency")
        T wrappedObj = getWrappedObject();
        return wrappedObj;
    }

    public <V> V perform(Function<T, V> function) {
        setWrappedObject(read());
        return function.apply(getWrappedObject());
    }

    @High
    public ResultSet execute(@High Statement statement) {
        statement.setConsistencyLevel(ConsistencyLevel.ALL);
        @SuppressWarnings("consistency")
        @High ResultSet result = getSession().execute(statement);
        return result;
    }

}
