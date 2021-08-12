import de.tuda.stg.consys.annotations.invariants.DataModel;
import java.lang.Void;

@DataModel
public class SimpleNumber{

    private int value;

    public SimpleNumber(int input) {
        value = input;
    }

    //@ assignable value;
    //@ ensures value == n;
    Void setValue(int n) {
        value = n;
        return null;
    }

    //@ assignable \nothing;
    //@ ensures \result == value;
    int getValue() {
        return value;
    }

    //@ assignable \nothing;
    //@ ensures \result == (n == value);
    boolean hasValue(int n) {
        return n == value;
    }

    //@ assignable \nothing;
    public boolean equals(Object o) {
        return o instanceof SimpleNumber && ((SimpleNumber) o).value == value;
    }



}