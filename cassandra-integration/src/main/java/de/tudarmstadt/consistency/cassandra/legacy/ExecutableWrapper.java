package de.tudarmstadt.consistency.cassandra.legacy;

import com.datastax.driver.core.ConsistencyLevel;
import com.datastax.driver.core.ResultSet;
import com.datastax.driver.core.Session;
import com.datastax.driver.core.Statement;

import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Supplier;

public abstract class ExecutableWrapper<T> extends ConsistencyWrapper<T> {

    private Session session;
    private Supplier<T> read;
    private Consumer<T> write;

    /**
     * @param wrappedObject
     * @param session The cassandra session associated with the wrapped object.
     * @param read A Supplier that should read the wrapped object from database.
     * @param write A Consumer that should write the wrapped object to database.
     * @param parent The ConsistencyObject object this wrapper is a member of.
     */
    public ExecutableWrapper(T wrappedObject,
                             Session session,
                             Supplier<T> read,
                             Consumer<T> write,
                             ConsistencyObject parent) {
        super(wrappedObject, parent);
        this.session = session;
        this.read = read;
        this.write = write;
    }


    /**
     * Performs a Function on the current wrapped object and returns the result.
     * May perform an update on the value before function execution.
     * @return The result of the Function call.
     */
    public abstract <V> V perform(Function<T, V> function);

    /**
     * @return The consistency level to use with execute(Statement).
     */
    abstract ConsistencyLevel getConsistencyLevel();

    /**
     * Executes the Cassandra statement with an appropriate consistency level
     * using this wrappers session.
     * @return ResultSet returned by the statement execution.
     */
    public ResultSet execute(Statement statement) {
        statement.setConsistencyLevel(this.getConsistencyLevel());
        return getSession().execute(statement);
    }

    /**
     * Executes the Supplier given to the constructor.
     * Should produce a value read from database.
     * Updates the wrapped object.
     * @return The wrapped object after execution of the Supplier.
     */
    T read() {
        setWrappedObject(this.read.get());
        return getWrappedObject();
    }

    /**
     * Executes the Consumer given to the constructor with the current wrapped object.
     * Should write the value to database.
     */
    void write() {
        this.write.accept(this.getWrappedObject());
    }

    @Override
    void setValue(T value, Scope scope){
        setWrappedObject(value);
        write();
    }

    /**
     * Executes the Supplier to read from database if no wrapped object is present.
     * Otherwise, executes the Consumer to write the wrapped object to database.
     */
    public void sync(){
        if(this.getWrappedObject() != null){
            this.write();
        } else {
            this.read();
        }
    }

    Session getSession() {
        return this.session;
    }
}
