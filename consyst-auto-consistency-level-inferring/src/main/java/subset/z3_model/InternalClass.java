package subset.z3_model;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import subset.Z3Checker;

import java.util.ArrayList;
import java.util.List;

/**
 * Data container that unites every relevant property of a replica of this class that the analysis
 * is interested about. These are:
 *
 * <p>1. State: initial state, state before method execution, state after method execution, state of
 * another replica that needs to merged with the own one <br>
 * 2. Variables: the values of the variables actually represent a certain state <br>
 * 3. Invariant constraints: properties that must hold in every state of the replica and must be
 * preserved by every method <br>
 * 4. Methods: operations that compute new states over the current state <br>
 * 5. Dedicated Merge Function: special method used that takes two states and returns a new one
 */
public class InternalClass {
  private String name;
  private BoolExpr initialValue;
  private BoolExpr invariant;
  private List<InternalVar> variables;
  private List<InternalMethod> methods;
  private InternalMergeFunction mergeFunction;

  private Expr[] oldState;
  private Expr[] otherState;
  private Expr[] newState;

  /**
   * Initializes a new internal object that represents a class of replicated objects. The initial
   * state constraints and invariant are initialized to true to express the following semantics: If
   * no additional constraints are added, this means that every state can be an initial state and
   * every state satisfies the invariant.
   */
  public InternalClass() {
    Context context = Z3Checker.context;
    initialValue = context.mkTrue();
    invariant = context.mkTrue();
    variables = new ArrayList<InternalVar>();
    methods = new ArrayList<InternalMethod>();
    // do not initialize merge in order to check if a merge has been found already
  }

  /**
   * This method initializes the state arrays that are later used to build up the formulas of the
   * property to prove. It must be called after all variables have already been added to the object.
   */
  public void initializeStates() {
    oldState = new Expr[variables.size()];
    otherState = new Expr[variables.size()];
    newState = new Expr[variables.size()];

    for (int i = 0; i < variables.size(); i++) {
      oldState[i] = variables.get(i).getOldValue();
      otherState[i] = variables.get(i).getOtherValue();
      newState[i] = variables.get(i).getNewValue();
    }
  }

  public BoolExpr getInitialValue() {
    return initialValue;
  }

  public BoolExpr getInvariant() {
    return invariant;
  }

  public List<InternalVar> getVariables() {
    return variables;
  }

  public List<InternalMethod> getMethods() {
    return methods;
  }

  public InternalMergeFunction getMergeFunction() {
    return mergeFunction;
  }

  public Expr[] getOldState() {
    return oldState;
  }

  public Expr[] getOtherState() {
    return otherState;
  }

  public Expr[] getNewState() {
    return newState;
  }

  /**
   * This method creates a new Z3 constant for every variable of this object and returns the array
   * that contains the copy for every variable of this object. The resulting array contains the
   * constants in the same order as {@link #getOldState()}, {@link #getNewState()} and {@link
   * #getOtherState()}.
   *
   * @param appendix String that is appended to every variable name so that it remains clear which
   *     state copy the new constants belong to if multiple copies are used in a formula
   * @return an array of new constants representing a new state for every variable
   */
  public Expr[] getFreshState(String appendix) {
    Expr[] freshState = new Expr[variables.size()];
    for (int i = 0; i < variables.size(); i++) {
      freshState[i] = variables.get(i).createCopy(appendix);
    }
    return freshState;
  }

  public void setName(String name) {
    this.name = name;
  }

  /**
   * Adds an invariant constraint to the currently built up invariant by conjoining them using
   * conjunction.
   *
   * @param invariant the new constraint to be added to the current one
   */
  public void addInvariantConstraint(BoolExpr invariant) {
    this.invariant = Z3Checker.context.mkAnd(this.invariant, invariant);
  }

  /**
   * Adds a new initial state constraint. There can be multiple initial states coming from multiple
   * constructors which is why a new constraint is conjoined by disjunction. If the current
   * constraint is true, then the current constraint is completely replaced by the incoming
   * constraint as a disjunction with true always yields true.
   *
   * @param init
   */
  public void addInitialState(BoolExpr init) {
    // if the initial state was true, it must be replaced
    if (initialValue.isTrue()) {
      initialValue = init;
    } else {
      // constraint from another constructor added with disjunction
      this.invariant = Z3Checker.context.mkOr(this.invariant, init);
    }
  }

  public void addVariable(InternalVar variable) {
    variables.add(variable);
  }

  public void addMethod(InternalMethod method) {
    methods.add(method);
  }

  /**
   * Adds an {@link InternalMergeFunction} object to this object if none has been added already.
   *
   * @param mergeFunction The merge function to be set to this object
   * @throws IllegalStateException if a merge function is tried to be added although there has been
   *     added another one already
   */
  public void addMerge(InternalMergeFunction mergeFunction) throws IllegalStateException {
    if (this.mergeFunction == null) this.mergeFunction = mergeFunction;
    else throw new IllegalStateException("cannot have multiple merge functions inside one class!");
  }
}
