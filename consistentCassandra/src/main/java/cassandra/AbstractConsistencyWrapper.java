package cassandra;

public abstract class AbstractConsistencyWrapper<T> {

    private T wrappedObject;

    public AbstractConsistencyWrapper(T wrappedObject){
        this.wrappedObject = wrappedObject;
    }

    public AbstractConsistencyWrapper(T wrappedObject, IntermediateWrapper parent){
        this(wrappedObject);
        parent.addWrapper(this);
    }

    public AbstractConsistencyWrapper(T wrappedObject, Wrappable parent){
        this(wrappedObject, parent.getWrapper());
    }

    void setWrappedObject(T wrappedObject) {
        this.wrappedObject = wrappedObject;
        write();
    }

    abstract void write();

    abstract T read();

    public T getWrappedObject(){
        return wrappedObject;
    }

    public abstract T value();
}
