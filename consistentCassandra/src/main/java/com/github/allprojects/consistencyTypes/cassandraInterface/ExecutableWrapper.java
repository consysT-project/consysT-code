package com.github.allprojects.consistencyTypes.cassandraInterface;

import com.datastax.driver.core.ConsistencyLevel;
import com.datastax.driver.core.ResultSet;
import com.datastax.driver.core.Session;
import com.datastax.driver.core.Statement;

import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Supplier;

public abstract class ExecutableWrapper<T> extends ConsistencyWrapper<T>{

    private Session session;
    private Supplier<T> read;
    private Consumer<T> write;

    public ExecutableWrapper(T wrappedObject,
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

    public abstract ConsistencyLevel getConsistencyLevel();

    public ResultSet execute(Statement statement) {
        statement.setConsistencyLevel(this.getConsistencyLevel());
        ResultSet result = getSession().execute(statement);
        return result;
    }

    T read() {
        setWrappedObject(this.read.get());
        return getWrappedObject();
    }

    void write() {
        this.write.accept(this.getWrappedObject());
    }

    public void setValue(T value, Scope scope){
        setWrappedObject(value);
        write();
    }

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
