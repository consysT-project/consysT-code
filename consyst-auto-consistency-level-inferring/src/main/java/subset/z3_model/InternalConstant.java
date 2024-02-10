package subset.z3_model;

import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;

/**
 * This class is used to represent final values. They only regard a type and a preset value that never changes.
 */
public class InternalConstant extends InternalVar {

    /**
     * Constructs a new final value representation
     * @param name name of the constant
     * @param sort sort of the constant
     */
    public InternalConstant(String name, Sort sort) {
        super();
        this.name = name;
        this.sort = sort;
    }

    /**
     * As this class represents final values, copies also yield the value directly
     * @param appendix is ignored
     * @return the value of the constant
     */
    @Override
    public Expr createCopy(String appendix) {
        return oldValue;
    }

    /**
     * Sets the value of the constant to the given one
     * @param value the value to set the constant to
     */
    public void setValue(Expr value) {
        this.oldValue = value;
        this.otherValue = value;
        this.newValue = value;
    }
}
