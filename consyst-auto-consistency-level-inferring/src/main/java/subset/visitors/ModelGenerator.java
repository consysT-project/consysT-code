package subset.visitors;

import com.microsoft.z3.ArraySort;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Expr;
import com.microsoft.z3.Sort;
import org.eclipse.jdt.internal.compiler.ASTVisitor;
import org.eclipse.jdt.internal.compiler.ast.*;
import org.eclipse.jdt.internal.compiler.lookup.ClassScope;
import org.eclipse.jdt.internal.compiler.lookup.MethodScope;
import org.jmlspecs.jml4.ast.*;
import subset.z3_model.*;

/**
 * This class visits a {@link org.jmlspecs.jml4.ast.JmlTypeDeclaration} and generates internal data
 * structures with {@link subset.z3_model.InternalClass} being the top definition that contain the
 * invariants, pre- and post-conditions in Z3 readable format.
 */
public class ModelGenerator extends ASTVisitor {
  private InternalClass result = new InternalClass();
  private InternalScope internalScope = new InternalScope();
  private FormulaGenerator formulaGenerator = new FormulaGenerator();
  private TypeGenerator typeGenerator = new TypeGenerator();
  private IntegerValueVisitor integerValueVisitor = new IntegerValueVisitor();


  /**
   * Visit the declaration of a class variable: <br>
   * 1. create internal variable representation <br>
   * 2. add to internal class <br>
   * 3. add to scope
   */
  @Override
  public boolean visit(FieldDeclaration fieldDeclaration, MethodScope scope) {
    // name and sort are needed for variable object
    String name = String.valueOf(fieldDeclaration.name);
    Sort sort = typeGenerator.visitTypeReference(fieldDeclaration.type);
    InternalVar variable;

    if (sort instanceof ArraySort) {
      // get size of array
      if (fieldDeclaration.initialization != null) {
        int arraySize =
            integerValueVisitor.visitExpression(
                ((ArrayAllocationExpression) fieldDeclaration.initialization).dimensions[0],
                internalScope);
        variable = new InternalArray(name, (ArraySort) sort, arraySize);
      } else {
        variable = new InternalArray(name, (ArraySort) sort);
      }
    }

    else {
      if (fieldDeclaration.binding.isFinal()) {
        variable = new InternalConstant(name, sort);
      } else {
        variable = new InternalVar(name, sort);
      }
    }

    // add variable to class
    result.addVariable(variable);

    // add variable to scope
    internalScope.addClassVariable(name, variable);

    // constant need to be initialized immediately
    if (variable instanceof InternalConstant) {
      Expr initialValue =
          formulaGenerator.visitExpression(fieldDeclaration.initialization, internalScope);
      if (initialValue != null) {
        ((InternalConstant) variable).setValue(initialValue);
      } else {
        throw new IllegalStateException("Constant value must be initialized directly!");
      }
    }
    return false;
  }

  /**
   * Visit constructor specification and set initialization constraints accordingly. Constraints
   * from multiple constructors are conjoined using disjunction.
   */
  @Override
  public boolean visit(JmlConstructorDeclaration jmlConstructorDeclaration, ClassScope scope) {
    // check if constructor has specifications
    if (jmlConstructorDeclaration.specification == null
        || jmlConstructorDeclaration.specification.getPostcondition() == null) {
      return false;
    }

    // translate postcondition
    Expr initExpr =
        formulaGenerator.visitExpression(
            jmlConstructorDeclaration.specification.getPostcondition(), internalScope);

    // add translated postcondition to result as disjunction
    if (initExpr instanceof BoolExpr) {
      result.addInitialState((BoolExpr) initExpr);
    }

    return false;
  }

  /**
   * Visit the declaration of a method:
   *
   * <p>1. distinguish between normal method and merge function <br>
   * 2. get arguments and add them to scope <br>
   * 3. get the return type and construct a return variable if necessary <br>
   * 4. visit the pre- and postcondition and add them to the internal method <br>
   * 5. remove arguments and return value from local scope
   */
  @Override
  public boolean visit(JmlMethodDeclaration methodDeclaration, ClassScope scope) {
    String methodName = String.valueOf(methodDeclaration.selector);
    if (methodName.equals("merge")) {
      visitMerge(methodDeclaration, scope);
      return false;
    }
    InternalMethod method = new InternalMethod(methodName);

    // arguments: get name and type of each argument and add them to method
    if (methodDeclaration.arguments != null) {
      for (Argument arg : methodDeclaration.arguments) {
        String name = String.valueOf(arg.name);
        Sort type = typeGenerator.visitTypeBinding(arg.type.resolveType(scope));
        method.addArgument(name, type);
        // add method argument to local scope
        internalScope.addLocalVariable(name, method.getArgument(name));
      }
    }

    // return type
    Sort returnType =
        typeGenerator.visitTypeBinding(methodDeclaration.returnType.resolveType(scope));
    if (returnType != null) {
      method.setReturnType(returnType);
      internalScope.setCurrentReturnVariable(method.getReturnVariable());
    }

    if (methodDeclaration.specification != null) {
      // specification
      Expr preCondition =
          formulaGenerator.visitExpression(
              methodDeclaration.specification.getPrecondition(), internalScope);
      Expr postCondition =
          formulaGenerator.visitExpression(
              methodDeclaration.specification.getPostcondition(), internalScope);
      if (preCondition instanceof BoolExpr) method.setPreCondition((BoolExpr) preCondition);
      if (postCondition instanceof BoolExpr) method.setPostCondition((BoolExpr) postCondition);

      // assignable clauses
      for (JmlSpecCase jmlSpecCase : methodDeclaration.specification.getSpecCases()) {
        if (jmlSpecCase.body.rest instanceof JmlSpecCaseRestAsClauseSeq) {
          for (JmlClause clause : ((JmlSpecCaseRestAsClauseSeq) jmlSpecCase.body.rest).clauses) {
            if (clause instanceof JmlAssignableClause) {
              method.addPostCondition(
                  formulaGenerator.visitJmlAssignableClause(
                      (JmlAssignableClause) clause, internalScope));
            }
          }
        }
      }
    }

    if (internalScope.getCurrentReturnExpression() != null) {
      method.setReturnExpression(internalScope.getCurrentReturnExpression());
      internalScope.addReturnValue(methodName, method.getReturnExpression());
    }

    result.addMethod(method);
    internalScope.clearLocalScope();
    return false;
  }

  /**
   * Visit the merge function of the class: <br>
   * 1. check that there is no other merge function already added <br>
   * 2. add merge function to class signature <br>
   * 3. signal scope that code visits inside merge -> support "other" <br>
   * 4. visit pre- and post-conditions </pr>
   */
  public void visitMerge(JmlMethodDeclaration jmlMethodDeclaration, ClassScope scope) {
    // 1. check that there is no other merge function
    if (result.getMergeFunction() != null) {
      throw new IllegalStateException("There may not be multiple merge functions!");
    }
    // add to class signature
    InternalMergeFunction merge = new InternalMergeFunction();
    result.addMerge(merge);

    // signal scope to be inside merge
    internalScope.insideMergeFunction = true;

    // specification
    Expr preCondition =
        formulaGenerator.visitExpression(
            jmlMethodDeclaration.specification.getPrecondition(), internalScope);
    Expr postCondition =
        formulaGenerator.visitExpression(
            jmlMethodDeclaration.specification.getPostcondition(), internalScope);
    if (preCondition instanceof BoolExpr) merge.setPreCondition((BoolExpr) preCondition);
    if (postCondition instanceof BoolExpr) merge.setPostCondition((BoolExpr) postCondition);
    internalScope.insideMergeFunction = false;
  }

  /**
   * Visit the whole class declaration. This is done at the end, as now all the class variables are
   * known. <br>
   * 1. set class name <br>
   * 2. visit invariant expression <br>
   * 3. use added variables to add them to different class states, that are used in the analysis
   * stage <br>
   */
  public void visit(JmlTypeDeclaration jmlTypeDeclaration, ClassScope scope) {
    // set name for class object
    result.setName(String.valueOf(jmlTypeDeclaration.name));
    Expression invariant = jmlTypeDeclaration.getInvariant();
    // get invariant for class
    Expr invariantExpression = formulaGenerator.visitExpression(invariant, internalScope);
    // add invariant to internal class construct
    if (invariantExpression instanceof BoolExpr) {
      result.addInvariantConstraint((BoolExpr) invariantExpression);
    }
    // add variables to class state
    result.initializeStates();
  }

  // visit the clause types -> assignable, ensures, requires
  // result Value -> jml local declaration

  public InternalClass getResult() {
    return result;
  }

  public void reset() {
    result = new InternalClass();
  }
}
