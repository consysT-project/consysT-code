package de.tuda.stg.consys.invariants;

import de.tuda.stg.consys.invariants.subset.ProgramConfig;
import de.tuda.stg.consys.invariants.subset.model.ProgramModel;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;

import java.time.*;

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
            //Paths.get("consys-invariants","InvariantExamples","Indigo","Player.java"),
            //Paths.get("consys-riak/src/main/java/com/readytalk/crdt/sets/GSet.java"),
            //Paths.get("consys-riak/src/main/java/com/readytalk/crdt/sets/TwoPhaseSetP.java"),
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
    //runChecker(config, new Path[] { Paths.get("consys-invariants","src", "main", "resources", "guava-14.0.1.jar") }, sources);

    Path[] benchSource = new Path[] {
            Paths.get("consys-invariants/InvariantExamples/BankAccountLWW/BankAccountLWW.java"),
            Paths.get("consys-invariants/InvariantExamples/Consensus/Consensus.java"),
            Paths.get("consys-invariants/InvariantExamples/DistributedLock/DistributedLock.java"),
            Paths.get("consys-invariants/InvariantExamples/GCounterCRDT/GCounterCRDT.java"),
            Paths.get("consys-invariants/InvariantExamples/PNCounterCRDT/PNCounterCRDT.java"),
            Paths.get("consys-invariants/InvariantExamples/ResettableCounterWithRound/ResettableCounterWithRound.java")


    };
    int numOfRounds = 10;
    double totalTime[] = new double[benchSource.length];
    for(int index = 0; index < benchSource.length; index += 1) {
      long startTime = System.currentTimeMillis();
      Path[] inputSource = new Path[1];
      inputSource[0] = benchSource[index];
      for(int round = 0; round < numOfRounds; round += 1) {
        runChecker(config, new Path[]{Paths.get("consys-invariants", "src", "main", "resources", "guava-14.0.1.jar")}, inputSource);
      }
      long endTime   = System.currentTimeMillis();
      totalTime[index] = ((double) endTime - startTime) / numOfRounds;
      System.out.println("Average verifying time for this use case: " + totalTime[index] + " ms");
    }
    System.out.println();
    System.out.println("-----------------------Benchmarks-----------------------");
    System.out.println();
    for(int index = 0; index < benchSource.length; index += 1) {
      System.out.println("Average verifying time for the use case " + benchSource[index].toString().substring(benchSource[index].toString().lastIndexOf('/') + 1) + ": " + totalTime[index] + " ms.");
    }
    /*
    Last result:
    Average verifying time for the use case BankAccountLWW.java: 125.4 ms.
    Average verifying time for the use case Consensus.java: 57.5 ms.
    Average verifying time for the use case DistributedLock.java: 49.6 ms.
    Average verifying time for the use case GCounterCRDT.java: 179.1 ms.
    Average verifying time for the use case PNCounterCRDT.java: 181.9 ms.
    Average verifying time for the use case ResettableCounterWithRound.java: 115.9 ms.
    */
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
