package com.github.allprojects.consistencyTypes.cassandraInterface;

public class ConsistencyWrapper<T> {

    private T wrappedObject;

    public ConsistencyWrapper(T wrappedObject) {
        setWrappedObject(wrappedObject);
    }

    public ConsistencyWrapper(T wrappedObject, IntermediateWrapper parent) {
        this(wrappedObject);
        parent.addWrapper(this);
    }

    public ConsistencyWrapper(T wrappedObject, Wrappable parent) {
        this(wrappedObject, parent.getWrapper());
    }

    T getWrappedObject() {
        return wrappedObject;
    }

    void setWrappedObject(T object) {
        this.wrappedObject = object;
    }

    public T value() {
        return value(new Scope());
    }

    T value(Scope scope) {
        return getWrappedObject();
    }

    public void setValue(T value) {
        setValue(value, new Scope());
    }

    void setValue(T value, Scope scope) {
        setWrappedObject(value);
    }
}
