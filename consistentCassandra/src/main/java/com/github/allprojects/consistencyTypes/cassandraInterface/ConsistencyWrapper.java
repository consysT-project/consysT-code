package com.github.allprojects.consistencyTypes.cassandraInterface;

/**
 * Parent class for all wrapper classes.
 * @param <T> The type of the wrapped object.
 */
public class ConsistencyWrapper<T> {

    private T wrappedObject;

    public ConsistencyWrapper(T wrappedObject) {
        setWrappedObject(wrappedObject);
    }

    public ConsistencyWrapper(T wrappedObject, IntermediateWrapper parent) {
        this(wrappedObject);
        parent.addWrapper(this);
    }

    public ConsistencyWrapper(T wrappedObject, ConsistencyObject parent) {
        this(wrappedObject, parent.getWrapper());
    }

    /**
     * Accessor to the wrapped object, only to be used by subclasses.
     */
    T getWrappedObject() {
        return wrappedObject;
    }

    /**
     * Accessor to the wrapped object, only to be used by subclasses.
     */
    void setWrappedObject(T object) {
        this.wrappedObject = object;
    }

    /**
     * API method for getting the current value of the wrapped object.
     * May perform an update on the value before returning it.
     *
     * When overriding, consider overriding value(Scope) instead.
     */
    public T value() {
        return value(new Scope());
    }

    T value(Scope scope) {
        return getWrappedObject();
    }

    /**
     * API method for setting the current value of the wrapped object.
     *
     * When overriding, consider overriding setValue(Scope) instead.
     */
    public void setValue(T value) {
        setValue(value, new Scope());
    }

    void setValue(T value, Scope scope) {
        setWrappedObject(value);
    }
}
