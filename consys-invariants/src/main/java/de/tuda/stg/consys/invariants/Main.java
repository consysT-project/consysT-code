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
    // other use cases: ------------------------------
    Path[] benchSource2 = new Path[] {
            Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/bankaccount/BankAccount.java"),
            Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/multicounter/SimpleNumber.java"),
            Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/multicounter/SimpleCounter.java"),
            Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/creditaccount/SequentialCounter.java"),
            Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/creditaccount/SequentialCreditAccount.java"),
            Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/creditaccount/ReplicatedCounter.java"),
            Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/creditaccount/ReplicatedCreditAccount.java"),
            Paths.get("consys-riak/src/main/java/com/readytalk/crdt/counters/GCounter.java"),
            Paths.get("consys-riak/src/main/java/com/readytalk/crdt/counters/PNCounter.java"),
            Paths.get("consys-riak/src/main/java/com/readytalk/crdt/sets/GSet.java"),
            Paths.get("consys-riak/src/main/java/com/readytalk/crdt/sets/TwoPhaseSet.java"),
            Paths.get("consys-riak/src/main/java/com/readytalk/crdt/sets/ORSet.java"),
    };
    // Simple use cases: -----------------------------
    int numOfRounds = 10;
    int extra = 9; // extra use cases other than benchSource singleClass use cases.
    double totalTime[] = new double[benchSource.length + extra];
    String classNames[] = new String[benchSource.length + extra];
    int index = 0;
    Path[] inputSource;
    for( ; index < benchSource.length; index += 1) {
      inputSource = new Path[1];
      inputSource[0] = benchSource[index];
      totalTime[index] = benchmark(config, inputSource, numOfRounds);
      classNames[index] = benchSource[index].toString().substring(benchSource[index].toString().lastIndexOf('/') + 1, benchSource[index].toString().length() - 5);
    }

    // Bank Account: ----------------------------------
    inputSource = new Path[1];
    inputSource[0] = benchSource2[0];
    totalTime[index] = benchmark(config, inputSource, numOfRounds);
    classNames[index] = "BankAccount";
    index += 1;
    // MultiClassCounter: ------------------------------------------
    inputSource = new Path[2];
    inputSource[0] = benchSource2[1];
    inputSource[1] = benchSource2[2];
    totalTime[index] = benchmark(config, inputSource, numOfRounds);
    classNames[index] = "MultiClassCounter";
    index += 1;
    // SequentialCreditAccount: ------------------------------------
    inputSource = new Path[2];
    inputSource[0] = benchSource2[3];
    inputSource[1] = benchSource2[4];
    totalTime[index] = benchmark(config, inputSource, numOfRounds);
    classNames[index] = "SequentialCreditAccount";
    index += 1;
    // ReplicatedCreditAccount: ------------------------------------
    inputSource = new Path[2];
    inputSource[0] = benchSource2[5];
    inputSource[1] = benchSource2[6];
    totalTime[index] = benchmark(config, inputSource, numOfRounds);
    classNames[index] = "ReplicatedCreditAccount";
    index += 1;
    // Riak-GCounter: ------------------------------------
    inputSource = new Path[1];
    inputSource[0] = benchSource2[7];
    totalTime[index] = benchmark(config, inputSource, numOfRounds);
    classNames[index] = "Riak:GCounter";
    index += 1;
    // ReplicatedCreditAccount: ------------------------------------
    inputSource = new Path[2];
    inputSource[0] = benchSource2[7];
    inputSource[1] = benchSource2[8];
    totalTime[index] = benchmark(config, inputSource, numOfRounds);
    classNames[index] = "Riak:PNCounter";
    index += 1;
    // Riak-GSet: ------------------------------------
    inputSource = new Path[1];
    inputSource[0] = benchSource2[9];
    totalTime[index] = benchmark(config, inputSource, numOfRounds);
    classNames[index] = "Riak:GSet";
    index += 1;
    // ReplicatedCreditAccount: ------------------------------------
    inputSource = new Path[2];
    inputSource[0] = benchSource2[9];
    inputSource[1] = benchSource2[10];
    totalTime[index] = benchmark(config, inputSource, numOfRounds);
    classNames[index] = "Riak:TwoPhaseSet";
    index += 1;
    // Riak-GSet: ------------------------------------
    inputSource = new Path[1];
    inputSource[0] = benchSource2[11];
    totalTime[index] = benchmark(config, inputSource, numOfRounds);
    classNames[index] = "Riak:ORSet";
    index += 1;
    // Printing: ------
    System.out.println();
    System.out.println("-----------------------Benchmarks-----------------------");
    System.out.println("Number of use cases: " + index);
    System.out.println("Number of rounds: " + numOfRounds);
    for(int ind = 0; ind < benchSource.length + extra; ind += 1) {
      System.out.println("Average verifying time for the use case " + classNames[ind] + ": " + totalTime[ind] + " ms.");
    }
    // Maybe Tournaments?
    /*
    Last result:
    Number of use cases: 15
    Number of rounds: 10
    Average verifying time for the use case BankAccountLWW: 112.7 ms.
    Average verifying time for the use case Consensus: 69.9 ms.
    Average verifying time for the use case DistributedLock: 42.2 ms.
    Average verifying time for the use case GCounterCRDT: 206.4 ms.
    Average verifying time for the use case PNCounterCRDT: 165.8 ms.
    Average verifying time for the use case ResettableCounterWithRound: 88.1 ms.
    Average verifying time for the use case BankAccount: 444.8 ms.
    Average verifying time for the use case MultiClassCounter: 86.8 ms.
    Average verifying time for the use case SequentialCreditAccount: 31.8 ms.
    Average verifying time for the use case ReplicatedCreditAccount: 500.3 ms.
    Average verifying time for the use case Riak:GCounter: 4361.4 ms.
    Average verifying time for the use case Riak:PNCounter: 301851.9 ms.
    Average verifying time for the use case Riak:GSet: 34.2 ms.
    Average verifying time for the use case Riak:TwoPhaseSet: 58.7 ms.
    Average verifying time for the use case Riak:ORSet: 54.7 ms.
    */
  }

  public static double benchmark(ProgramConfig config, Path[] sources, int numberOfRounds) {
    long startTime = System.currentTimeMillis();
    for(int round = 0; round < numberOfRounds; round += 1) {
      runChecker(config, new Path[]{Paths.get("consys-invariants", "src", "main", "resources", "guava-14.0.1.jar")}, sources);
    }
    long endTime = System.currentTimeMillis();
    double result = ((double) endTime - startTime) / numberOfRounds;
    return result;
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
