package cassandra;

public abstract class AbstractConsistencyWrapper<T> {

    private T wrappedObject;

    public AbstractConsistencyWrapper(T wrappedObject){
        setWrappedObject(wrappedObject);
        write(new Scope());
    }

    public AbstractConsistencyWrapper(T wrappedObject, IntermediateWrapper parent){
        this(wrappedObject);
        parent.addWrapper(this);
    }

    public AbstractConsistencyWrapper(T wrappedObject, Wrappable parent){
        this(wrappedObject, parent.getWrapper());
    }

    abstract void write(Scope t);

    abstract T read(Scope t);

    T getWrappedObject(){
        return wrappedObject;
    }

    void setWrappedObject(T object){
        this.wrappedObject = object;
    }

    public abstract T value();

    public void setValue(T value) {
        setWrappedObject(value);
        write(new Scope());
    }
}
