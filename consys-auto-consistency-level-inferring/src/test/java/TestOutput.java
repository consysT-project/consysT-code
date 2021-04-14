import org.eclipse.jdt.core.compiler.CompilationProgress;
import org.eclipse.jdt.internal.compiler.ast.TypeDeclaration;
import org.jmlspecs.jml4.ast.JmlTypeDeclaration;
import org.junit.jupiter.api.Test;
import subset.Z3Checker;
import subset.visitors.ModelGenerator;
import subset.z3_model.InternalClass;

import java.io.PrintWriter;
import java.util.List;
import java.util.Map;

// DYLD_LIBRARY_PATH=/Users/benyamin/WorkspacePhD/Mirko_invariant_edited/pre_and_post_conditions/lib/
// DYLD_LIBRARY_PATH=/Users/benyamin/WorkspacePhD/ConSysT2/consysT-code/consys-auto-consistency-level-inferring/lib/
// For environment variables

public class TestOutput {

    org.eclipse.jdt.internal.compiler.batch.Main compilerStarter =
            new org.eclipse.jdt.internal.compiler.batch.Main(
                    new PrintWriter(System.out),
                    new PrintWriter(System.err),
                    false,
                    (Map) null,
                    (CompilationProgress) null);

    String[] simpleBankAccount = {"src/main/resources/test/SimpleBankAccount.java"};
    String[] consensus = {"src/main/resources/test/Consensus.java"};
    String[] counterCRDT = {"src/main/resources/test/CounterCRDT.java"};
    String[] counter = {"src/main/resources/test/Counter.java"};
    String[] distributedLock = {"src/main/resources/test/DistributedLock.java"};
    String[] resettableCounter = {"src/main/resources/test/ResettableCounter.java"};
    String[] resettableCounterWithRound = {"src/main/resources/test/ResettableCounterWithRound.java"};
    String[] any = {"src/main/resources/test/BankAccount.java"};

    ModelGenerator visitor = new ModelGenerator();




//    @Test
//    public void testSimpleBankAccount() {
//        compilerStarter.compile(simpleBankAccount);
//
//        assert compilerStarter.batchCompiler.parser.compilationUnit.types != null;
//        TypeDeclaration simpleBankAccount = compilerStarter.batchCompiler.parser.compilationUnit.types[0];
//        simpleBankAccount.traverse(visitor, simpleBankAccount.scope);
//        visitor.visit((JmlTypeDeclaration) simpleBankAccount, simpleBankAccount.scope);
//        InternalClass result = visitor.getResult();
//        visitor.reset();
//
//        Z3Checker.modelPrint = false;
//        System.out.println("initial state: " + Z3Checker.checkInitialState(result));
//        System.out.println("invariant sufficiency: " + Z3Checker.checkInvariantSufficiency(result));
//        System.out.println("merge idempotency: " + Z3Checker.checkMergeIdempotency(result));
//        System.out.println("merge commutativity: " + Z3Checker.checkMergeCommutativity(result));
//        System.out.println("merge associativity: " + Z3Checker.checkMergeAssociativity(result));
//
//        System.out.println("self mergeability: " + Z3Checker.checkSelfMergeable(result));
//        System.out.println("invariant sufficient merge: " + Z3Checker.checkInvariantSufficientMerge(result));
//        System.out.println("mergeable merged state: " + Z3Checker.checkMergeableMergedState(result));
//
//        Map<String, Z3Checker.ConsistencyLevel> weakOrStrong =
//                Z3Checker.checkWeakConsistencyForMethods(result);
//        Map<String, Z3Checker.Monotonicity> monotonicity =
//                Z3Checker.checkMonotonicityForMethods(result);
//        Map<String, List<String>> mergeability =
//                Z3Checker.checkMergeabilityForMethods(result);
//
//        System.out.println(weakOrStrong.toString());
//        System.out.println(monotonicity.toString());
//        System.out.println(mergeability.toString());
//    }

    @Test
    public void testCounterCRDTComplete() {
        compilerStarter.compile(counterCRDT);

        assert compilerStarter.batchCompiler.parser.compilationUnit.types != null;
        TypeDeclaration counterCRDT = compilerStarter.batchCompiler.parser.compilationUnit.types[0];
        counterCRDT.traverse(visitor, counterCRDT.scope);
        visitor.visit((JmlTypeDeclaration) counterCRDT, counterCRDT.scope);
        InternalClass result = visitor.getResult();
        visitor.reset();

        Z3Checker.modelPrint = false;
        System.out.println(Z3Checker.checkInitialState(result));
        System.out.println(Z3Checker.checkInvariantSufficiency(result));
        System.out.println(Z3Checker.checkMergeIdempotency(result));
        System.out.println(Z3Checker.checkMergeCommutativity(result));
        System.out.println(Z3Checker.checkMergeAssociativity(result));
        System.out.println(Z3Checker.checkSelfMergeable(result));
        System.out.println(Z3Checker.checkInvariantSufficientMerge(result));
        System.out.println(Z3Checker.checkMergeableMergedState(result));

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
    public void testCounterComplete() {
        compilerStarter.compile(counter);

        assert compilerStarter.batchCompiler.parser.compilationUnit.types != null;
        TypeDeclaration counter = compilerStarter.batchCompiler.parser.compilationUnit.types[0];
        counter.traverse(visitor, counter.scope);
        visitor.visit((JmlTypeDeclaration) counter, counter.scope);
        InternalClass result = visitor.getResult();
        visitor.reset();

        Z3Checker.modelPrint = false;
        System.out.println(Z3Checker.checkInitialState(result));
        System.out.println(Z3Checker.checkInvariantSufficiency(result));
        System.out.println(Z3Checker.checkMergeIdempotency(result));
        System.out.println(Z3Checker.checkMergeCommutativity(result));
        System.out.println(Z3Checker.checkMergeAssociativity(result));
        System.out.println(Z3Checker.checkSelfMergeable(result));
        System.out.println(Z3Checker.checkInvariantSufficientMerge(result));
        System.out.println(Z3Checker.checkMergeableMergedState(result));
        // check if sequential execution and the must have properties of the merge function hold
        System.out.println("Prerequisities okay?: " + Z3Checker.checkPreRequisities(result));

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
    public void testConsensusComplete() {
        compilerStarter.compile(consensus);

        assert compilerStarter.batchCompiler.parser.compilationUnit.types != null;
        TypeDeclaration counterClass = compilerStarter.batchCompiler.parser.compilationUnit.types[0];
        counterClass.traverse(visitor, counterClass.scope);
        visitor.visit((JmlTypeDeclaration) counterClass, counterClass.scope);
        InternalClass result = visitor.getResult();
        visitor.reset();

        Z3Checker.modelPrint = false;
        System.out.println(Z3Checker.checkInitialState(result));
        System.out.println(Z3Checker.checkInvariantSufficiency(result));
        System.out.println(Z3Checker.checkMergeIdempotency(result));
        System.out.println(Z3Checker.checkMergeCommutativity(result));
        System.out.println(Z3Checker.checkMergeAssociativity(result));
        System.out.println(Z3Checker.checkSelfMergeable(result));
        System.out.println(Z3Checker.checkInvariantSufficientMerge(result));
        System.out.println(Z3Checker.checkMergeableMergedState(result));


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
    public void testDistributedLockComplete() {
        compilerStarter.compile(distributedLock);

        assert compilerStarter.batchCompiler.parser.compilationUnit.types != null;
        TypeDeclaration distributedLock = compilerStarter.batchCompiler.parser.compilationUnit.types[0];
        distributedLock.traverse(visitor, distributedLock.scope);
        visitor.visit((JmlTypeDeclaration) distributedLock, distributedLock.scope);
        InternalClass result = visitor.getResult();
        visitor.reset();

        Z3Checker.modelPrint = false;
        System.out.println(Z3Checker.checkInitialState(result));
        System.out.println(Z3Checker.checkInvariantSufficiency(result));
        System.out.println(Z3Checker.checkMergeIdempotency(result));
        System.out.println(Z3Checker.checkMergeCommutativity(result));
        System.out.println(Z3Checker.checkMergeAssociativity(result));
        System.out.println(Z3Checker.checkSelfMergeable(result));
        System.out.println(Z3Checker.checkInvariantSufficientMerge(result));
        System.out.println(Z3Checker.checkMergeableMergedState(result));

        System.out.println("Prerequisities okay?: " + Z3Checker.checkPreRequisities(result));

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
    public void testResettableCounterComplete() {
        compilerStarter.compile(resettableCounter);

        assert compilerStarter.batchCompiler.parser.compilationUnit.types != null;
        TypeDeclaration resettableCounter =
                compilerStarter.batchCompiler.parser.compilationUnit.types[0];
        resettableCounter.traverse(visitor, resettableCounter.scope);
        visitor.visit((JmlTypeDeclaration) resettableCounter, resettableCounter.scope);
        InternalClass result = visitor.getResult();
        visitor.reset();

        Z3Checker.modelPrint = false;
        System.out.println(Z3Checker.checkInitialState(result));
        System.out.println(Z3Checker.checkInvariantSufficiency(result));
        System.out.println(Z3Checker.checkMergeIdempotency(result));
        System.out.println(Z3Checker.checkMergeCommutativity(result));
        System.out.println(Z3Checker.checkMergeAssociativity(result));
        System.out.println(Z3Checker.checkSelfMergeable(result));
        System.out.println(Z3Checker.checkInvariantSufficientMerge(result));
        System.out.println(Z3Checker.checkMergeableMergedState(result));

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

        Z3Checker.modelPrint = false;
        System.out.println(Z3Checker.checkInitialState(result));
        System.out.println(Z3Checker.checkInvariantSufficiency(result));
        System.out.println(Z3Checker.checkMergeIdempotency(result));
        System.out.println(Z3Checker.checkMergeCommutativity(result));
        System.out.println(Z3Checker.checkMergeAssociativity(result));
        System.out.println(Z3Checker.checkSelfMergeable(result));
        System.out.println(Z3Checker.checkInvariantSufficientMerge(result));
        System.out.println(Z3Checker.checkMergeableMergedState(result));

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
    public void testAnyOtherClass() {
        compilerStarter.compile(any);

        assert compilerStarter.batchCompiler.parser.compilationUnit.types != null;
        TypeDeclaration simpleBankAccount = compilerStarter.batchCompiler.parser.compilationUnit.types[0];
        simpleBankAccount.traverse(visitor, simpleBankAccount.scope);
        visitor.visit((JmlTypeDeclaration) simpleBankAccount, simpleBankAccount.scope);
        InternalClass result = visitor.getResult();
        visitor.reset();

        Z3Checker.modelPrint = false;
        System.out.println("initial state: " + Z3Checker.checkInitialState(result));
        System.out.println("merge idempotency: " + Z3Checker.checkMergeIdempotency(result));
        System.out.println("merge commutativity: " + Z3Checker.checkMergeCommutativity(result));
        System.out.println("merge associativity: " + Z3Checker.checkMergeAssociativity(result));

        System.out.println("self mergeability: " + Z3Checker.checkSelfMergeable(result));
        System.out.println("invariant sufficient merge: " + Z3Checker.checkInvariantSufficientMerge(result));
        System.out.println("mergeable merged state: " + Z3Checker.checkMergeableMergedState(result));

        Map<String, Z3Checker.InvariantSufficiency> invariantSufficiencyMap =
                Z3Checker.checkInvariantSufficiencyForMethods(result);
        Map<String, Z3Checker.ConsistencyLevel> weakOrStrong =
                Z3Checker.checkWeakConsistencyForMethods(result);
        Map<String, Z3Checker.Monotonicity> monotonicity =
                Z3Checker.checkMonotonicityForMethods(result);
        Map<String, List<String>> mergeability =
                Z3Checker.checkMergeabilityForMethods(result);

        System.out.println();
        System.out.println(invariantSufficiencyMap);
        System.out.println(weakOrStrong.toString());
        System.out.println(monotonicity.toString());
        System.out.println(mergeability.toString());
    }



}
