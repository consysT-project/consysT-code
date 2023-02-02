package de.tuda.stg.consys.invariants.solver;

import com.google.common.collect.Maps;
import de.tuda.stg.consys.logging.Logger;

import javax.tools.JavaCompiler;
import javax.tools.ToolProvider;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Map;

public class CompilerBenchmark {

	private interface RunnerFactory {
		Runnable create(Path[] paths);
	}

	private static class SysRunnerFactory implements RunnerFactory {

		private static class SysRunner implements Runnable {
			private final Path[] paths;

			private SysRunner(Path[] paths) {
				this.paths = paths;
			}

			@Override
			public void run() {
				try {
					Main.runChecker(Examples.STATEFUL_CONFIG, new Path[]{
									Paths.get("consys-invariants", "src", "main", "resources", "guava-14.0.1.jar"),
							},
							paths
					);
				} catch (Exception e) {
					e.printStackTrace();
				}
			}
		}

		@Override
		public Runnable create(Path[] paths) {
			return new SysRunner(paths);
		}
	}

	private static class JavaRunnerFactory implements RunnerFactory {

		private static class JavaRunner implements Runnable {
			private final String[] files;
			private final JavaCompiler compiler;

			private JavaRunner(String[] files) {
				this.files = files;
				compiler = ToolProvider.getSystemJavaCompiler();
			}

			@Override
			public void run() {
				compiler.run(null, null, null, files);
			}
		}

		@Override
		public Runnable create(Path[] paths) {

			var pathStrings = new String[paths.length];
			for (int i = 0; i < paths.length; i++) {
				pathStrings[i] = paths[i].toString();
			}

			return new JavaRunner(pathStrings);
		}
	}


	public static Map<String, Double> runSysBench() {
		return runBench(new SysRunnerFactory());
	}

	public static Map<String, Double> runJavaBench() {
		return runBench(new JavaRunnerFactory());
	}

	public static Map<String, Double> runBench(RunnerFactory runnerFactory) {

		int numOfMeasures = 10;
		int numOfWarmup = 10;

		Map<String, Double> results = Maps.newHashMap();

		for (var entry : Main.CASE_STUDIES.entrySet()) {
			Logger.info("Benchmark " + entry.getKey());

			Logger.info("Run warmups: " + numOfWarmup);
			benchmark(runnerFactory, entry.getValue(), numOfWarmup);

			Logger.info("Run measures: " + numOfMeasures);
			var result = benchmark(runnerFactory, entry.getValue(), numOfMeasures);

			results.put(entry.getKey(), result);
		}

		return results;
	}





	public static double benchmark(RunnerFactory runnerFactory, Path[] sources, int numberOfRounds) {
		double result = 0;

		for(int i = 0; i < numberOfRounds; i++) {
			Logger.info("iteration " + (i + 1));

			System.gc();
			try {
				//Wait for garbage collection.
				Thread.sleep(3000);
			} catch (InterruptedException e) {
				throw new RuntimeException(e);
			}

			var runner = runnerFactory.create(sources);

			long startTime = System.nanoTime();
			runner.run();
			long endTime = System.nanoTime();

			result = result + ((double) endTime - startTime) / numberOfRounds;
		}

		return result;
	}
}


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
Average verifying time for the use case JointBankAccount: 24.4 ms.
Average verifying time for the use case TwoPhaseSet: 27.9 ms.

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
Average verifying time for the use case JointBankAccount: 17.0 ms.
Average verifying time for the use case TwoPhaseSet: 17.3 ms.

    */