package de.tuda.stg.consys.invariants;

import de.tuda.stg.consys.invariants.subset.model.ProgramModel;
import org.eclipse.jdt.internal.compiler.ast.TypeDeclaration;
import org.eclipse.jdt.internal.compiler.parser.Parser;
import org.jmlspecs.jml4.ast.JmlTypeDeclaration;

import java.nio.file.Path;
import java.nio.file.Paths;

/**
 * This class represents the starting point of the whole analysis. The analysis consists of the
 * following steps:
 *
 * <p>1. compile JML annotated Java code <br>
 * 2. extract compilation units of compiled code <br>
 * 3. transform Java+JML AST into internal data structures that use Z3 acceptable formulas <br>
 * 4. use internal data structures to build formulas that depict the properties to be proven <br>
 * 5. start Z3 to prove if the properties hold or not <br>
 */
public class Main {

  public static void main(String[] args) {
    // Set the source file
    Path[] sources = new Path[] {
            //Paths.get("consys-invariants", "InvariantExamples", "BankAccountCRDT", "BankAccountCRDT.java"),
            // Paths.get("consys-invariants", "InvariantExamples", "BankAccount", "BankAccount.java")
            //    Paths.get("consys-invariants", "InvariantExamples", "Consensus", "Consensus.java")
            //Paths.get("consys-invariants", "InvariantExamples", "CounterCRDT", "CounterCRDT.java")
            Paths.get("consys-invariants", "InvariantExamples", "GCounterCRDT", "GCounterCRDT.java")
            //  Paths.get("consys-invariants", "InvariantExamples", "GSetCRDT", "GSetCRDT.java")
              //Paths.get("consys-invariants", "InvariantExamples", "DistributedLock", "DistributedLock.java")
            // Paths.get("consys-invariants", "InvariantExamples", "ResettableCounter", "ResettableCounter.java")
           // Paths.get("consys-invariants", "InvariantExamples", "ResettableCounterWithRound", "ResettableCounterWithRound.java")
            //   Paths.get("consys-invariants", "InvariantExamples", "ResettableCounterWithRound", "ResettableCounterWithRound.java")
//            Paths.get("consys-invariants","InvariantExamples","MultiClassTestExample","SimpleCounter.java")
//            Paths.get("consys-invariants","InvariantExamples","MultiClassTestExample","SimpleNumber.java")
            //  Paths.get("consys-invariants","InvariantExamples","Indigo","Tournaments.java")
           // Paths.get("consys-riak/src/main/java/com/readytalk/crdt/counters/GCounter.java")
    };

    runChecker(sources);
  }

  public static void runChecker(Path[] sources) {
    // Compile the file to ASTs
    CompilerBinding compiler = new CompilerBinding();
    Parser compiledParser = compiler.compile(sources);

    // Create the program model
    ProgramModel model = new ProgramModel(compiledParser);
    model.loadParsedClasses();
    // Check the classes
    model.checkAll();
  }


}
