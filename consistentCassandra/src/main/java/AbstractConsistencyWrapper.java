import com.datastax.driver.core.*;

import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Supplier;

public abstract class AbstractConsistencyWrapper<T> {

    private T wrappedObject;
    private ConsistentCassandraConnector connector;
    private Supplier<T> read;
    private Consumer<T> write;

    public AbstractConsistencyWrapper(T wrappedObject, ConsistentCassandraConnector connector,
                                      Supplier<T> read,
                                      Consumer<T> write){
        this.wrappedObject = wrappedObject;
        this.connector = connector;
        this.read = read;
        this.write = write;
    }

    public abstract T value();

    public abstract <V> V perform(Function<T, V> function);

    public abstract ResultSet execute(Statement statement);

    T read() {
        return this.read.get();
    };

    void write() {
        this.write.accept(this.value());
    };

    void setWrappedObject(T wrappedObject) {
        this.wrappedObject = wrappedObject;
        write();
    }

    T getWrappedObject() {
        return this.wrappedObject;
    }

    ConsistentCassandraConnector getConnector() {
        return this.connector;
    }

    Session getSession() {
        return this.connector.getSession();
    }
}
