package cassandra;

public abstract class Wrappable {

    private IntermediateWrapper wrapper;

    public Wrappable(){
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
