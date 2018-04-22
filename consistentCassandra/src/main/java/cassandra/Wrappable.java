package cassandra;

public abstract class Wrappable {

    private IntermediateWrapper wrapper;

    public Wrappable(){
        this.wrapper = new IntermediateWrapper(this);
    }

    public IntermediateWrapper getWrapper() {
        return wrapper;
    }
}
