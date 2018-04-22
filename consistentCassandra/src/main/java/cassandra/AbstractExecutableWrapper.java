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

    public abstract T value();

    public abstract <V> V perform(Function<T, V> function);

    public abstract ResultSet execute(Statement statement);

    T read() {
        return this.read.get();
    };

    void write() {
        this.write.accept(this.value());
    };

    Session getSession() {
        return this.session;
    }
}
