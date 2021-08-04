import de.tuda.stg.consys.annotations.invariants.DataModel;

@DataModel
public class SimpleNumber{

    private int value;

    public SimpleNumber(int input) {
        value = input;
    }

    void setValue(int n) {
        value = n;
    }

    int getValue() {
        return value;
    }

    void modify(int change) {
        value += change;
    }

    boolean hasValue(int n) {
        return n == value;
    }

    @Override
    public boolean equals(Object o) {
        return o instanceof SimpleNumber && ((SimpleNumber) o).value == value;
    }



}