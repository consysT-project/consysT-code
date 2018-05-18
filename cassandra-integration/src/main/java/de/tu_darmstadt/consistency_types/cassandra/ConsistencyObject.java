package de.tu_darmstadt.consistency_types.cassandra;

/**
 * This class should be inherited from by any class that wraps some of its members in ConsitencyWrappers.
 * @see ConsistencyWrapper
 */
public abstract class ConsistencyObject {

    private IntermediateWrapper wrapper;

    public ConsistencyObject(){
        this.wrapper = new IntermediateWrapper<>(this);
    }

    public IntermediateWrapper getWrapper() {
        return wrapper;
    }

    public void read() {
        Scope scope = new Scope();
        scope.read(this.getWrapper());
    }

    public void write() {
        Scope scope = new Scope();
        scope.write(this.getWrapper());
    }
}