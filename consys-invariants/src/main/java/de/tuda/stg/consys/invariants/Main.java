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
            Paths.get("consys-riak/src/main/java/com/readytalk/crdt/counters/GCounter.java"),
            Paths.get("consys-riak/src/main/java/com/readytalk/crdt/counters/PNCounter.java")
            //Paths.get("consys-riak/src/main/java/com/readytalk/crdt/sets/GSet.java"),
            //Paths.get("consys-riak/src/main/java/com/readytalk/crdt/sets/TwoPhaseSet.java")
            //Paths.get("consys-riak/src/main/java/com/readytalk/crdt/sets/ORSet.java")
            //Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/tournament/Player.java"),
            //Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/tournament/GSetPlayer.java"),
            //Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/tournament/TwoPhaseSetPlayer.java"),
            //Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/tournament/Tournament.java"),
            //Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/tournament/GSetTournament.java"),
            //Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/tournament/TwoPhaseSetTournament.java"),
            //Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/tournament/Tournaments.java")
    };
    runChecker(config, new Path[] { Paths.get("consys-invariants","src", "main", "resources", "guava-14.0.1.jar") }, sources);


    // -------------------------------------------------------Start part of benchmarks:-------------------------------------------------------

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
            Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/gset/GSet.java"),
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
            Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/tournament/Player.java"),
            Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/tournament/GSetPlayer.java"),
            Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/tournament/TwoPhaseSetPlayer.java"),
            Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/tournament/Tournament.java"),
            Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/tournament/GSetTournament.java"),
            Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/tournament/TwoPhaseSetTournament.java"),
            Paths.get("consys-invariants/src/main/examples/de/tuda/stg/consys/invariants/examples/tournament/Tournaments.java")
    };

    int numOfRounds = 10; // change it for benchmarks
    int extra = 11; // extra use cases other than benchSource singleClass use cases.
    double totalTime[] = new double[benchSource.length + extra];
    String classNames[] = new String[benchSource.length + extra];
    int index = 0;
    Path[] inputSource;
    // Some runes before measuring time: ----------------------
    for(int i = 0; numOfRounds > 0 && i < benchSource.length; i += 1){
      Path[] tmp = new Path[1];
      tmp[0] = benchSource[i];
      benchmark(config, tmp, 3 );
    }
    // Simple use cases: -----------------------------
    for( ; index < benchSource.length; index += 1) {
      inputSource = new Path[1];
      inputSource[0] = benchSource[index];
      totalTime[index] = benchmark(config, inputSource, numOfRounds);
      classNames[index] = benchSource[index].toString().substring(benchSource[index].toString().lastIndexOf('/') + 1, benchSource[index].toString().length() - 5);
    }
    // GSet: ----------------------------------
    inputSource = new Path[1];
    inputSource[0] = benchSource2[0];
    totalTime[index] = benchmark(config, inputSource, numOfRounds);
    classNames[index] = "GSet";
    index += 1;
    // Bank Account: ----------------------------------
    inputSource = new Path[1];
    inputSource[0] = benchSource2[1];
    totalTime[index] = benchmark(config, inputSource, numOfRounds);
    classNames[index] = "BankAccount";
    index += 1;
    // MultiClassCounter: ------------------------------------------
    inputSource = new Path[2];
    inputSource[0] = benchSource2[2];
    inputSource[1] = benchSource2[3];
    totalTime[index] = benchmark(config, inputSource, numOfRounds);
    classNames[index] = "MultiClassCounter";
    index += 1;
    // SequentialCreditAccount: ------------------------------------
    inputSource = new Path[2];
    inputSource[0] = benchSource2[4];
    inputSource[1] = benchSource2[5];
    totalTime[index] = benchmark(config, inputSource, numOfRounds);
    classNames[index] = "SequentialCreditAccount";
    index += 1;
    // ReplicatedCreditAccount: ------------------------------------
    inputSource = new Path[2];
    inputSource[0] = benchSource2[6];
    inputSource[1] = benchSource2[7];
    totalTime[index] = benchmark(config, inputSource, numOfRounds);
    classNames[index] = "ReplicatedCreditAccount";
    index += 1;
    // Riak-GCounter: ------------------------------------
    inputSource = new Path[1];
    inputSource[0] = benchSource2[8];
    totalTime[index] = benchmark(config, inputSource, numOfRounds);
    classNames[index] = "Riak:GCounter";
    index += 1;
    // Riak-PNCounter: ------------------------------------
    inputSource = new Path[2];
    inputSource[0] = benchSource2[8];
    inputSource[1] = benchSource2[9];
    totalTime[index] = benchmark(config, inputSource, numOfRounds);
    classNames[index] = "Riak:PNCounter";
    index += 1;
    // Riak-GSet: ------------------------------------
    inputSource = new Path[1];
    inputSource[0] = benchSource2[10];
    totalTime[index] = benchmark(config, inputSource, numOfRounds);
    classNames[index] = "Riak:GSet";
    index += 1;
    // Riak-TwoPhaseSet: ------------------------------------
    inputSource = new Path[2];
    inputSource[0] = benchSource2[10];
    inputSource[1] = benchSource2[11];
    totalTime[index] = benchmark(config, inputSource, numOfRounds);
    classNames[index] = "Riak:TwoPhaseSet";
    index += 1;
    // Riak-ORSet: ------------------------------------
    inputSource = new Path[1];
    inputSource[0] = benchSource2[12];
    totalTime[index] = benchmark(config, inputSource, numOfRounds);
    classNames[index] = "Riak:ORSet";
    index += 1;
    // Tournaments: ------------------------------------
    inputSource = new Path[7];
    for(int i = 0; i < 7; i += 1) inputSource[i] = benchSource2[13 + i];
    totalTime[index] = benchmark(config, inputSource, numOfRounds);
    classNames[index] = "Tournaments";
    index += 1;
    // Printing: ---------------------------------------
    if(numOfRounds > 0) {
      System.out.println();
      System.out.println("-----------------------Benchmarks-----------------------");
      System.out.println("Number of use cases: " + index);
      System.out.println("Number of rounds: " + numOfRounds);
      for (int ind = 0; ind < benchSource.length + extra; ind += 1) {
        System.out.println("Average verifying time for the use case " + classNames[ind] + ": " + totalTime[ind] + " ms.");
      }
    }
    // Maybe Tournaments?
    /*
    Last result:
-----------------------Benchmarks-----------------------
Number of use cases: 17
Number of rounds: 10
Average verifying time for the use case BankAccountLWW: 30.0 ms.
Average verifying time for the use case Consensus: 34.5 ms.
Average verifying time for the use case DistributedLock: 39.7 ms.
Average verifying time for the use case GCounterCRDT: 162.1 ms.
Average verifying time for the use case PNCounterCRDT: 162.9 ms.
Average verifying time for the use case ResettableCounterWithRound: 86.7 ms.
Average verifying time for the use case GSet: 27.1 ms.
Average verifying time for the use case BankAccount: 440.6 ms.
Average verifying time for the use case MultiClassCounter: 94.6 ms.
Average verifying time for the use case SequentialCreditAccount: 28.9 ms.
Average verifying time for the use case ReplicatedCreditAccount: 504.3 ms.
Average verifying time for the use case Riak:GCounter: 113.2 ms.
Average verifying time for the use case Riak:PNCounter: 111.6 ms.
Average verifying time for the use case Riak:GSet: 36.5 ms.
Average verifying time for the use case Riak:TwoPhaseSet: 63.3 ms.
Average verifying time for the use case Riak:ORSet: 54.3 ms.
Average verifying time for the use case Tournaments: 48.2 ms.

    Last result for compiling:

-----------------------Benchmarks-----------------------
Number of use cases: 17
Number of rounds: 10
Average verifying time for the use case BankAccountLWW: 22.8 ms.
Average verifying time for the use case Consensus: 28.3 ms.
Average verifying time for the use case DistributedLock: 15.3 ms.
Average verifying time for the use case GCounterCRDT: 18.3 ms.
Average verifying time for the use case PNCounterCRDT: 19.5 ms.
Average verifying time for the use case ResettableCounterWithRound: 12.4 ms.
Average verifying time for the use case GSet: 18.5 ms.
Average verifying time for the use case BankAccount: 26.1 ms.
Average verifying time for the use case MultiClassCounter: 22.0 ms.
Average verifying time for the use case SequentialCreditAccount: 15.7 ms.
Average verifying time for the use case ReplicatedCreditAccount: 17.8 ms.
Average verifying time for the use case Riak:GCounter: 26.4 ms.
Average verifying time for the use case Riak:PNCounter: 31.2 ms.
Average verifying time for the use case Riak:GSet: 24.5 ms.
Average verifying time for the use case Riak:TwoPhaseSet: 33.2 ms.
Average verifying time for the use case Riak:ORSet: 32.9 ms.
Average verifying time for the use case Tournaments: 36.2 ms.

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
    //var model = new ProgramModel(compileResult, config);
    //model.loadParsedClasses();

    // Check the classes
    //model.checkAll();
  }


}
