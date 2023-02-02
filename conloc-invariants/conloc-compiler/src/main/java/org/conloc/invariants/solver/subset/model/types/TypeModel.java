package org.conloc.invariants.solver.subset.model.types;

import com.microsoft.z3.Sort;

import java.util.Optional;

public interface TypeModel<S extends Sort> {
    S toSort();

    /**
     * @return True, if this model can be converted to a sort.
     */
    default boolean hasSort() {
        return true;
    }

    default Optional<S> getSort() {
        if (hasSort()) return Optional.of(toSort());
        else return Optional.empty();
    }
}
