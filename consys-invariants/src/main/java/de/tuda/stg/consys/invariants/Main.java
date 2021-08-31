package de.tuda.stg.consys.invariants;

import de.tuda.stg.consys.invariants.subset.ProgramConfig;
import de.tuda.stg.consys.invariants.subset.model.ProgramModel;

import java.io.IOException;
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



  public static void main(String[] args) throws IOException {

    //ProgramConfig config = Examples.DEFAULT_CONFIG;
    ProgramConfig config = Examples.STATEFUL_CONFIG;

    // Set the source file
    Path[] sources = new Path[] {
//            Paths.get("consys-invariants", "InvariantExamples", "BankAccountCRDT", "BankAccountCRDT.java"),
            // Paths.get("consys-invariants", "InvariantExamples", "BankAccount", "BankAccount.java")
            //    Paths.get("consys-invariants", "InvariantExamples", "Consensus", "Consensus.java")
            //Paths.get("consys-invariants", "InvariantExamples", "CounterCRDT", "CounterCRDT.java")
//            Paths.get("consys-invariants", "InvariantExamples", "GCounterCRDT", "GCounterCRDT.java")
            //  Paths.get("consys-invariants", "InvariantExamples", "GSetCRDT", "GSetCRDT.java")
              //Paths.get("consys-invariants", "InvariantExamples", "DistributedLock", "DistributedLock.java")
            // Paths.get("consys-invariants", "InvariantExamples", "ResettableCounter", "ResettableCounter.java")
           // Paths.get("consys-invariants", "InvariantExamples", "ResettableCounterWithRound", "ResettableCounterWithRound.java")
            //   Paths.get("consys-invariants", "InvariantExamples", "ResettableCounterWithRound", "ResettableCounterWithRound.java")
            //Paths.get("consys-invariants","InvariantExamples","MultiClassTestExample","SimpleNumber.java"),
            //Paths.get("consys-invariants","InvariantExamples","MultiClassTestExample","SimpleCounter.java"),
            Paths.get("consys-invariants","InvariantExamples","Indigo","Player.java"),
            Paths.get("consys-riak/src/main/java/com/readytalk/crdt/sets/GSet.java"),
            Paths.get("consys-riak/src/main/java/com/readytalk/crdt/sets/TwoPhaseSetP.java"),
            //Paths.get("consys-invariants","InvariantExamples","Indigo","Tournament.java"),
            //Paths.get("consys-riak/src/main/java/com/readytalk/crdt/sets/TwoPhaseSetT.java"),
              //Paths.get("consys-riak/src/main/java/com/readytalk/crdt/sets/GSet.java"),
              //Paths.get("consys-riak/src/main/java/com/readytalk/crdt/sets/TwoPhaseSet.java"),
              //Paths.get("consys-invariants","InvariantExamples","Indigo","Player.java"),
              //Paths.get("consys-invariants","InvariantExamples","Indigo","Tournament.java"),
              //Paths.get("consys-invariants","InvariantExamples","Indigo","Tournaments.java")
            //Paths.get("consys-riak/src/main/java/com/readytalk/crdt/counters/GCounter.java"),
            //Paths.get("consys-riak/src/main/java/com/readytalk/crdt/counters/PNCounter.java")
            //Paths.get("consys-riak/src/main/java/com/readytalk/crdt/sets/GSet.java"),
            //Paths.get("consys-riak/src/main/java/com/readytalk/crdt/sets/TwoPhaseSet.java")
            //Paths.get("consys-riak/src/main/java/com/readytalk/crdt/sets/ORSet.java")
    };

    runChecker(config, new Path[] { Paths.get("consys-invariants","src", "main", "resources", "guava-14.0.1.jar") }, sources);
  }

  public static void runChecker(ProgramConfig config, Path[] additionalClasspath, Path[] sources) {
    // Compile the file to ASTs
    var compileResult = CompilerBinding.compile(additionalClasspath, sources);

    // Create the program modelconsys
    var model = new ProgramModel(compileResult, config);
    model.loadParsedClasses();

    // Check the classes
    model.checkAll();
  }


}
