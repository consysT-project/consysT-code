package cassandra;

import com.datastax.driver.core.*;

import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Supplier;

public abstract class AbstractExecutableWrapper<T> extends AbstractConsistencyWrapper<T>{

    private Session session;
    private Supplier<T> read;
    private Consumer<T> write;

    public AbstractExecutableWrapper(T wrappedObject,
                                     Session session,
                                     Supplier<T> read,
                                     Consumer<T> write,
                                     Wrappable parent){
        super(wrappedObject, parent);
        this.session = session;
        this.read = read;
        this.write = write;
    }

    public abstract <V> V perform(Function<T, V> function);

    public abstract ResultSet execute(Statement statement);

    T read() {
        setWrappedObject(this.read.get());
        return getWrappedObject();
    };

    void write() {
        this.write.accept(this.getWrappedObject());
    };

    Session getSession() {
        return this.session;
    }
}
