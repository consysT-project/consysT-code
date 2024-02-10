import org.eclipse.jdt.core.compiler.CompilationProgress;
import org.eclipse.jdt.internal.compiler.ast.TypeDeclaration;
import org.jmlspecs.jml4.ast.JmlTypeDeclaration;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import subset.Z3Checker;
import subset.visitors.ModelGenerator;
import subset.z3_model.InternalClass;
import subset.z3_model.InternalMethod;

import java.io.PrintWriter;
import java.util.List;
import java.util.Map;

public class TestZ3Analysis {

  org.eclipse.jdt.internal.compiler.batch.Main compilerStarter =
      new org.eclipse.jdt.internal.compiler.batch.Main(
          new PrintWriter(System.out),
          new PrintWriter(System.err),
          false,
          (Map) null,
          (CompilationProgress) null);
  String[] counter = {"src/main/resources/test/Counter.java"};
  String[] consensus = {"src/main/resources/test/Consensus.java"};
  String[] distributedLock = {"src/main/resources/test/DistributedLock.java"};
  String[] resettableCounter = {"src/main/resources/test/ResettableCounter.java"};
  String[] resettableCounterWithRound = {"src/main/resources/test/ResettableCounterWithRound.java"};
  String[] counterCRDT = {"src/main/resources/test/CounterCRDT.java"};
  String[] sideEffects = {"src/main/resources/test/SideEffects.java"};
  String[] assignable = {"src/main/resources/test/Assignable.java"};
  String[] bankAccount = {"src/main/resources/test/BankAccount.java"};
  String[] simpleBankAccount = {"src/main/resources/test/SimpleBankAccount.java"};

  ModelGenerator visitor = new ModelGenerator();

  @Test
  public void testCounterComplete() {
    compilerStarter.compile(counter);

    assert compilerStarter.batchCompiler.parser.compilationUnit.types != null;
    TypeDeclaration counterClass = compilerStarter.batchCompiler.parser.compilationUnit.types[0];
    counterClass.traverse(visitor, counterClass.scope);
    visitor.visit((JmlTypeDeclaration) counterClass, counterClass.scope);
    InternalClass result = visitor.getResult();
    visitor.reset();

    // should hold
    Assertions.assertTrue(Z3Checker.checkInitialState(result));
    // should hold for all methods
    Assertions.assertTrue(Z3Checker.checkInvariantSufficiency(result));
    // merge is idempotent: old || other -> both are equal
    Assertions.assertTrue(Z3Checker.checkMergeIdempotency(result));
    /*
    not commutative because no notion of time of arrival
    -> or does not enforce the new value to stay the same
     */
    Assertions.assertFalse(Z3Checker.checkMergeCommutativity(result));
    /* same as commutativity */
    Assertions.assertFalse(Z3Checker.checkMergeAssociativity(result));
    /* precondition of merge is true*/
    Assertions.assertTrue(Z3Checker.checkSelfMergeable(result));
    /*
    true because invariant holds in old and other state and
    merge only assigns to values where the invariant is proven to hold
    */
    Assertions.assertTrue(Z3Checker.checkInvariantSufficientMerge(result));
    /*
    merge precondition is true and like above, old and new satisfy
    the invariant after merge
     */
    Assertions.assertTrue(Z3Checker.checkMergeableMergedState(result));

    /* ******************************** Method wise *************************************** */
    assert result.getMethods().size() == 3;
    InternalMethod inc = result.getMethods().get(0);
    InternalMethod dec = result.getMethods().get(1);
    InternalMethod getValue = result.getMethods().get(2);

    /*
    holds for all because merge precondition is true and they satisfy the
    invariant under sequential execution.
     */
    Assertions.assertTrue(Z3Checker.checkMergeableOperationState(result, inc));
    Assertions.assertTrue(Z3Checker.checkMergeableOperationState(result, getValue));
    Assertions.assertTrue(Z3Checker.checkMergeableOperationState(result, dec));

    Map<String, Z3Checker.Monotonicity> monotonicity =
            Z3Checker.checkMonotonicityForMethods(result);
    Map<String, List<String>> mergeability =
            Z3Checker.checkMergeabilityForMethods(result);

    /*
    monotonicity: merging new after method execution is new again
    getValue: new = old, so merge(old, old) = old = new
    dec: new = old-1, postMerge = old or new -> not monotone because of non-determinism
    inc: new = old+1, postMerge = old or new -> not monotone because of non-determinism
        -> non-determinism: postMerge does not always choose new state
     */
    System.out.println(monotonicity.toString());
    /*
    mergeability: resulting state of merges of two method executions holds the invariant
    every state after method execution mergeable with every other state
        -> merged state is chosen to be either m1 or m2 each holds the invariant for itself
     */
    System.out.println(mergeability.toString());
  }

  @Test
  public void testConsensusComplete() {
    compilerStarter.compile(consensus);

    assert compilerStarter.batchCompiler.parser.compilationUnit.types != null;
    TypeDeclaration counterClass = compilerStarter.batchCompiler.parser.compilationUnit.types[0];
    counterClass.traverse(visitor, counterClass.scope);
    visitor.visit((JmlTypeDeclaration) counterClass, counterClass.scope);
    InternalClass result = visitor.getResult();
    visitor.reset();

    /*
    valid by construction, because flag is false
     */
    Assertions.assertTrue(Z3Checker.checkInitialState(result));
    /*
    mark satisfies the invariant, because either flag is false
      or some field is set to true, which preserves the invariant
    agree satisfies the invariant because it requires all fields to
      be true and then sets the flag
     */
    Assertions.assertTrue(Z3Checker.checkInvariantSufficiency(result));
    /*
    no merge precondition to satisfy,
    new == (old || other) is idempotent, comm and assocative because of OR
     */
    Assertions.assertTrue(Z3Checker.checkMergeIdempotency(result));
    Assertions.assertTrue(Z3Checker.checkMergeCommutativity(result));
    Assertions.assertTrue(Z3Checker.checkMergeAssociativity(result));
    /*
    merge precondition is true
     */
    Assertions.assertTrue(Z3Checker.checkSelfMergeable(result));
    /*
    OR computes an upper bound of invariant sufficient states
    -> preserves invariant
     */
    Assertions.assertTrue(Z3Checker.checkInvariantSufficientMerge(result));
    /*
    pre merge is true, rest follows from invariant suff. merge
     */
    Assertions.assertTrue(Z3Checker.checkMergeableMergedState(result));


    Map<String, Z3Checker.ConsistencyLevel> weakOrStrong =
        Z3Checker.checkWeakConsistencyForMethods(result);
    for (Map.Entry<String, Z3Checker.ConsistencyLevel> e : weakOrStrong.entrySet()) {
      /*
      merge precondition is true, rest follows from invariant preservation under
      sequential execution
       */
      Assertions.assertEquals(e.getValue(), Z3Checker.ConsistencyLevel.WEAK);
    }

    Map<String, Z3Checker.Monotonicity> monotonicity =
            Z3Checker.checkMonotonicityForMethods(result);
    Map<String, List<String>> mergeability =
            Z3Checker.checkMergeabilityForMethods(result);

    /*
    {agree=WEAK, mark=WEAK}
    {agree=[], mark=[]}
     */

    /*
    monotonicity: merging new after method execution is new again
    mark: sets index to true -> will be seen in pairwise OR operation
    agree: sets flag to true -> will be seen in pairwise OR operation
    => both monotone
     */
    System.out.println(monotonicity.toString());
    /*
    mergeability: resulting state of merges of two method executions holds the invariant
    nothing reset to false -> every combination invariant preserving
     */
    System.out.println(mergeability.toString());
  }

  @Test
  public void testDistributedLockComplete() {
    compilerStarter.compile(distributedLock);

    assert compilerStarter.batchCompiler.parser.compilationUnit.types != null;
    TypeDeclaration distributedLock = compilerStarter.batchCompiler.parser.compilationUnit.types[0];
    distributedLock.traverse(visitor, distributedLock.scope);
    visitor.visit((JmlTypeDeclaration) distributedLock, distributedLock.scope);
    InternalClass result = visitor.getResult();
    visitor.reset();

    /*
    holds by construction: lock[0] is the only one set to true
     */
    Assertions.assertTrue(Z3Checker.checkInitialState(result));
    /*
    holds for transfer: requires own lock to be set, disables lock, gives it some other
    -> still exactly one lock present
     */
    Assertions.assertTrue(Z3Checker.checkInvariantSufficiency(result));
    /*
    all holds because deterministic either one or the other state is selected
    where the selected state has the highest timestamp value
     */
    Assertions.assertTrue(Z3Checker.checkMergeIdempotency(result));
    Assertions.assertTrue(Z3Checker.checkMergeCommutativity(result));
    Assertions.assertTrue(Z3Checker.checkMergeAssociativity(result));

    /*
    holds because precondition tests equality which is trivially true for one same state
     */
    Assertions.assertTrue(Z3Checker.checkSelfMergeable(result));
    /*
    holds because old and other satisfy the invariant and new is only set to one of them
     */
    Assertions.assertTrue(Z3Checker.checkInvariantSufficientMerge(result));
    /*
    I(new): holds, see invariant sufficient merge
    I(other): always holds because of lhs of formula
    pre_merge(new, other) || pre_merge(new, old): critical because of 2nd requires clause
         -> pre merge is hard to translate to the general case
     */
    Assertions.assertFalse(Z3Checker.checkMergeableMergedState(result));

    Map<String, Z3Checker.ConsistencyLevel> weakOrStrong =
            Z3Checker.checkWeakConsistencyForMethods(result);
    for (Map.Entry<String, Z3Checker.ConsistencyLevel> e : weakOrStrong.entrySet()) {
      /*
      I(new) follows from sequential execution, I(other) holds bc of lhs
      pre_merge(new, other) because new is only defined in terms of old
       */
      Assertions.assertEquals(e.getValue(), Z3Checker.ConsistencyLevel.WEAK);
    }

    Map<String, Z3Checker.Monotonicity> monotonicity =
            Z3Checker.checkMonotonicityForMethods(result);
    Map<String, List<String>> mergeability =
            Z3Checker.checkMergeabilityForMethods(result);

    /*
    {transfer=WEAK}
    {transfer=[]}
     */

    /*
    monotonicity: merging old with new after method execution is new again
    transfer monotone: new state is always selected because timestamp is greater than for old state
     */
    System.out.println(monotonicity.toString());
    /*
    mergeability: resulting state of merges of two method executions holds the invariant
    transfer executable concurrently: the state with higher timestamp completely selected, thus
    preserving the invariant by requirement
     */
    System.out.println(mergeability.toString());

  }

  @Test
  public void testResettableCounterComplete() {
    compilerStarter.compile(resettableCounter);

    assert compilerStarter.batchCompiler.parser.compilationUnit.types != null;
    TypeDeclaration resettableCounter =
        compilerStarter.batchCompiler.parser.compilationUnit.types[0];
    resettableCounter.traverse(visitor, resettableCounter.scope);
    visitor.visit((JmlTypeDeclaration) resettableCounter, resettableCounter.scope);
    InternalClass result = visitor.getResult();
    visitor.reset();

    /*
    holds because all fields are initialized to 0 >= 0
     */
    Assertions.assertTrue(Z3Checker.checkInitialState(result));
    /*
    holds for inc: only incrementing which remains >= 0, rest stays equal
    holds for reset: every field reset to 0 = 0
    holds for getValue, because no side effects
     */
    Assertions.assertTrue(Z3Checker.checkInvariantSufficiency(result));

    /*
    all 3 hold: new is set to either old or other, depending which value is greater
     */
    Assertions.assertTrue(Z3Checker.checkMergeIdempotency(result));
    Assertions.assertTrue(Z3Checker.checkMergeCommutativity(result));
    Assertions.assertTrue(Z3Checker.checkMergeAssociativity(result));

    /*
    holds because pre_merge is true
     */
    Assertions.assertTrue(Z3Checker.checkSelfMergeable(result));
    /*
    holds because is set to either of the sets that satisfy the invariant by definition
     */
    Assertions.assertTrue(Z3Checker.checkInvariantSufficientMerge(result));
    /*
    pre_merge is true -> same as invariant sufficient merge
     */
    Assertions.assertTrue(Z3Checker.checkMergeableMergedState(result));

    Map<String, Z3Checker.ConsistencyLevel> weakOrStrong =
            Z3Checker.checkWeakConsistencyForMethods(result);
    for (Map.Entry<String, Z3Checker.ConsistencyLevel> e : weakOrStrong.entrySet()) {
      /*
      pre_merge is true -> same as sequential execution
       */
      Assertions.assertEquals(e.getValue(), Z3Checker.ConsistencyLevel.WEAK);
    }

    Map<String, Z3Checker.Monotonicity> monotonicity =
            Z3Checker.checkMonotonicityForMethods(result);
    Map<String, List<String>> mergeability =
            Z3Checker.checkMergeabilityForMethods(result);

    /*
    {getValue=WEAK, reset=STRONG, inc=WEAK}
    {getValue=[], reset=[], inc=[]}
     */

    /*
    monotonicity: merging new after method execution is new again
    getValue: new = old -> merge = old = new
    inc: new > old -> merge = new
    reset: new <= old -> merge = old and not always new
     */
    System.out.println(monotonicity.toString());
    /*
    mergeability: resulting state of merges of two method executions holds the invariant
    merge selects state with higher inc -> no calculation that uses both states
        => every method mergeable with the others
     */
    System.out.println(mergeability.toString());
  }

  @Test
  public void testResettableCounterWithRoundComplete() {
    compilerStarter.compile(resettableCounterWithRound);

    assert compilerStarter.batchCompiler.parser.compilationUnit.types != null;
    TypeDeclaration resettableCounterWithRound =
        compilerStarter.batchCompiler.parser.compilationUnit.types[0];
    resettableCounterWithRound.traverse(visitor, resettableCounterWithRound.scope);
    visitor.visit(
        (JmlTypeDeclaration) resettableCounterWithRound, resettableCounterWithRound.scope);
    InternalClass result = visitor.getResult();
    visitor.reset();

    /*
    round initialized to 0 >= 0
    incs fields initialized to 0 >= 0
     */
    Assertions.assertTrue(Z3Checker.checkInitialState(result));
    /*
    holds for inc: only one value increment, rest stays the same
    holds for reset: round increment, rest set to 0
     */
    Assertions.assertTrue(Z3Checker.checkInvariantSufficiency(result));
    /*
    hold because new is set to either old or other depending on the greater value
     */
    Assertions.assertTrue(Z3Checker.checkMergeIdempotency(result));
    Assertions.assertTrue(Z3Checker.checkMergeCommutativity(result));
    Assertions.assertTrue(Z3Checker.checkMergeAssociativity(result));

    /*
    holds because pre_merge is true
     */
    Assertions.assertTrue(Z3Checker.checkSelfMergeable(result));
    /*
    holds because new is updates to either old or other, which both are required to satisfy
    the invariant
     */
    Assertions.assertTrue(Z3Checker.checkInvariantSufficientMerge(result));

    /*
    no merge precondition -> same as invariant sufficient merge
     */
    Assertions.assertTrue(Z3Checker.checkMergeableMergedState(result));

    Map<String, Z3Checker.ConsistencyLevel> weakOrStrong =
            Z3Checker.checkWeakConsistencyForMethods(result);
    for (Map.Entry<String, Z3Checker.ConsistencyLevel> e : weakOrStrong.entrySet()) {
      /*
      no merge precondition -> same as sequential execution
       */
      Assertions.assertEquals(e.getValue(), Z3Checker.ConsistencyLevel.WEAK);
    }

    Map<String, Z3Checker.Monotonicity> monotonicity =
            Z3Checker.checkMonotonicityForMethods(result);
    Map<String, List<String>> mergeability =
            Z3Checker.checkMergeabilityForMethods(result);

    /*
    {getValue=WEAK, reset=WEAK, inc=WEAK}
    {getValue=[], reset=[], inc=[]}
     */

    /*
    monotonicity: merging new after method execution is new again
    getValue: old = new -> merge = old = new bc of idempotency
    inc: new = old+1 -> merge will select new state
    reset: new reset > old reset -> merge will select new state
     */
    System.out.println(monotonicity.toString());
    /*
    mergeability: resulting state of merges of two method executions holds the invariant
        merge selects state with higher inc -> no calculation that uses both states or
            "partial update" that uses half the state of old and half of other
        => every method mergeable with the others
     */
    System.out.println(mergeability.toString());
  }

  @Test
  public void testCounterCRDTComplete() {
    compilerStarter.compile(counterCRDT);

    assert compilerStarter.batchCompiler.parser.compilationUnit.types != null;
    TypeDeclaration counterCRDT = compilerStarter.batchCompiler.parser.compilationUnit.types[0];
    counterCRDT.traverse(visitor, counterCRDT.scope);
    visitor.visit((JmlTypeDeclaration) counterCRDT, counterCRDT.scope);
    InternalClass result = visitor.getResult();
    visitor.reset();

    /*
    holds because all fields are set to 0 and 0-0 = 0
     */
    Assertions.assertTrue(Z3Checker.checkInitialState(result));
    /*
    holds for getValue: no side effects
    holds for inc: only increment own field, no other updates
    holds for dec: only decrement if sum >= 1, no other updates
     */
    Assertions.assertTrue(Z3Checker.checkInvariantSufficiency(result));

    /*
    hold because new state is updated to state which is greater
     */
    Assertions.assertTrue(Z3Checker.checkMergeIdempotency(result));
    Assertions.assertTrue(Z3Checker.checkMergeCommutativity(result));
    Assertions.assertTrue(Z3Checker.checkMergeAssociativity(result));

    /*
    holds because pre_merge is true
     */
    Assertions.assertTrue(Z3Checker.checkSelfMergeable(result));
    /*
    holds because for both inc and dec the highest values are used and invariant held
    for old and other
     */
    Assertions.assertTrue(Z3Checker.checkInvariantSufficientMerge(result));
    /*
    pre_merge is true -> same as invariant sufficient merge
     */
    Assertions.assertTrue(Z3Checker.checkMergeableMergedState(result));

    Map<String, Z3Checker.ConsistencyLevel> weakOrStrong =
            Z3Checker.checkWeakConsistencyForMethods(result);
    for (Map.Entry<String, Z3Checker.ConsistencyLevel> e : weakOrStrong.entrySet()) {
      /*
      pre_merge is true -> same as sequential execution
       */
      Assertions.assertEquals(e.getValue(), Z3Checker.ConsistencyLevel.WEAK);
    }

    Map<String, Z3Checker.Monotonicity> monotonicity =
            Z3Checker.checkMonotonicityForMethods(result);
    Map<String, List<String>> mergeability =
            Z3Checker.checkMergeabilityForMethods(result);

    /*
    {getValue=WEAK, dec=WEAK, inc=WEAK}
    {getValue=[], dec=[], inc=[]}
     */

    /*
    monotonicity: merging new after method execution is new again
    getValue: old = new -> merge = old = new bc idempotency
    inc: new incs > old -> merge wil select new incs, decs remains same
    dec: new decs > old -> merge will select new decs, decs remains same
     */
    System.out.println(monotonicity.toString());
    /*
    mergeability: resulting state of merges of two method executions holds the invariant
    merge will always select the bigger values for incs and decs -> preserving the invariant
    for either combination of methods, because methods are only executed in a valid
    prestate
    -> no chaining of decs, instead both operate on sum == 1 in worst case
     */
    System.out.println(mergeability.toString());
  }

  @Test
  public void testSideEffectsComplete() {
    compilerStarter.compile(sideEffects);

    assert compilerStarter.batchCompiler.parser.compilationUnit.types != null;
    TypeDeclaration sideEffects = compilerStarter.batchCompiler.parser.compilationUnit.types[0];
    sideEffects.traverse(visitor, sideEffects.scope);
    visitor.visit((JmlTypeDeclaration) sideEffects, sideEffects.scope);
    InternalClass result = visitor.getResult();
    visitor.reset();

    Z3Checker.modelPrint = false;
    System.out.println("initial state: " + Z3Checker.checkInitialState(result));
    System.out.println("invariant sufficiency: " + Z3Checker.checkInvariantSufficiency(result));
    System.out.println("merge idempotency: " + Z3Checker.checkMergeIdempotency(result));
    System.out.println("merge commutativity: " + Z3Checker.checkMergeCommutativity(result));
    System.out.println("merge associativity: " + Z3Checker.checkMergeAssociativity(result));
    System.out.println("self mergeability: " + Z3Checker.checkSelfMergeable(result));
    System.out.println("invariant sufficient merge: " + Z3Checker.checkInvariantSufficientMerge(result));
    System.out.println("mergeable merged state: " + Z3Checker.checkMergeableMergedState(result));

    Map<String, Z3Checker.ConsistencyLevel> weakOrStrong =
            Z3Checker.checkWeakConsistencyForMethods(result);
    Map<String, Z3Checker.Monotonicity> monotonicity =
            Z3Checker.checkMonotonicityForMethods(result);
    Map<String, List<String>> mergeability =
            Z3Checker.checkMergeabilityForMethods(result);

    System.out.println(weakOrStrong.toString());
    System.out.println(monotonicity.toString());
    System.out.println(mergeability.toString());
  }

  @Test
  public void testAssignableComplete() {
    compilerStarter.compile(assignable);

    assert compilerStarter.batchCompiler.parser.compilationUnit.types != null;
    TypeDeclaration assignable = compilerStarter.batchCompiler.parser.compilationUnit.types[0];
    assignable.traverse(visitor, assignable.scope);
    visitor.visit((JmlTypeDeclaration) assignable, assignable.scope);
    InternalClass result = visitor.getResult();
    visitor.reset();

    Z3Checker.modelPrint = false;
    System.out.println("initial state: " + Z3Checker.checkInitialState(result));
    System.out.println("invariant sufficiency: " + Z3Checker.checkInvariantSufficiency(result));
    System.out.println("merge idempotency: " + Z3Checker.checkMergeIdempotency(result));
    System.out.println("merge commutativity: " + Z3Checker.checkMergeCommutativity(result));
    System.out.println("merge associativity: " + Z3Checker.checkMergeAssociativity(result));
    System.out.println("self mergeability: " + Z3Checker.checkSelfMergeable(result));
    System.out.println("invariant sufficient merge: " + Z3Checker.checkInvariantSufficientMerge(result));
    System.out.println("mergeable merged state: " + Z3Checker.checkMergeableMergedState(result));

    Map<String, Z3Checker.ConsistencyLevel> weakOrStrong =
            Z3Checker.checkWeakConsistencyForMethods(result);
    Map<String, Z3Checker.Monotonicity> monotonicity =
            Z3Checker.checkMonotonicityForMethods(result);
    Map<String, List<String>> mergeability =
            Z3Checker.checkMergeabilityForMethods(result);

    System.out.println(weakOrStrong.toString());
    System.out.println(monotonicity.toString());
    System.out.println(mergeability.toString());
  }

  @Test
  public void testBankAccountComplete() {
    compilerStarter.compile(bankAccount);

    assert compilerStarter.batchCompiler.parser.compilationUnit.types != null;
    TypeDeclaration bankAccount = compilerStarter.batchCompiler.parser.compilationUnit.types[0];
    bankAccount.traverse(visitor, bankAccount.scope);
    visitor.visit((JmlTypeDeclaration) bankAccount, bankAccount.scope);
    InternalClass result = visitor.getResult();
    visitor.reset();

    Z3Checker.modelPrint = false;
    System.out.println("initial state: " + Z3Checker.checkInitialState(result));
    System.out.println("invariant sufficiency: " + Z3Checker.checkInvariantSufficiency(result));
    System.out.println("merge idempotency: " + Z3Checker.checkMergeIdempotency(result));
    System.out.println("merge commutativity: " + Z3Checker.checkMergeCommutativity(result));
    System.out.println("merge associativity: " + Z3Checker.checkMergeAssociativity(result));
    System.out.println("self mergeability: " + Z3Checker.checkSelfMergeable(result));
    System.out.println("invariant sufficient merge: " + Z3Checker.checkInvariantSufficientMerge(result));
    System.out.println("mergeable merged state: " + Z3Checker.checkMergeableMergedState(result));

    Map<String, Z3Checker.ConsistencyLevel> weakOrStrong =
            Z3Checker.checkWeakConsistencyForMethods(result);
    Map<String, Z3Checker.Monotonicity> monotonicity =
            Z3Checker.checkMonotonicityForMethods(result);
    Map<String, List<String>> mergeability =
            Z3Checker.checkMergeabilityForMethods(result);

    System.out.println(weakOrStrong.toString());
    System.out.println(monotonicity.toString());
    System.out.println(mergeability.toString());
  }

  @Test
  public void testSimpleBankAccount() {
    compilerStarter.compile(simpleBankAccount);

    assert compilerStarter.batchCompiler.parser.compilationUnit.types != null;
    TypeDeclaration simpleBankAccount = compilerStarter.batchCompiler.parser.compilationUnit.types[0];
    simpleBankAccount.traverse(visitor, simpleBankAccount.scope);
    visitor.visit((JmlTypeDeclaration) simpleBankAccount, simpleBankAccount.scope);
    InternalClass result = visitor.getResult();
    visitor.reset();

    Z3Checker.modelPrint = false;
    System.out.println("initial state: " + Z3Checker.checkInitialState(result));
    System.out.println("invariant sufficiency: " + Z3Checker.checkInvariantSufficiency(result));
    System.out.println("merge idempotency: " + Z3Checker.checkMergeIdempotency(result));
    System.out.println("merge commutativity: " + Z3Checker.checkMergeCommutativity(result));
    System.out.println("merge associativity: " + Z3Checker.checkMergeAssociativity(result));
    System.out.println("self mergeability: " + Z3Checker.checkSelfMergeable(result));
    System.out.println("invariant sufficient merge: " + Z3Checker.checkInvariantSufficientMerge(result));
    System.out.println("mergeable merged state: " + Z3Checker.checkMergeableMergedState(result));

    Map<String, Z3Checker.ConsistencyLevel> weakOrStrong =
            Z3Checker.checkWeakConsistencyForMethods(result);
    Map<String, Z3Checker.Monotonicity> monotonicity =
            Z3Checker.checkMonotonicityForMethods(result);
    Map<String, List<String>> mergeability =
            Z3Checker.checkMergeabilityForMethods(result);

    System.out.println(weakOrStrong.toString());
    System.out.println(monotonicity.toString());
    System.out.println(mergeability.toString());
  }
}
