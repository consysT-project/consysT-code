package de.tuda.stg.consys.invariants.subset.z3_model;

/**
 * Internal representation of merge functions. They are also methods but need to be considered
 * separately later on in the analysis, which is why they are described using an own class.
 */
public class InternalMergeFunction extends InternalMethod {
  public InternalMergeFunction() {
    super("merge");
  }
}
