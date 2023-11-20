package de.tuda.stg.consys.invariants.solver;

import com.google.common.collect.Maps;
import de.tuda.stg.consys.invariants.solver.subset.ClassProperties;
import de.tuda.stg.consys.invariants.solver.subset.ProgramConfig;
import de.tuda.stg.consys.invariants.solver.subset.model.ProgramModel;
import de.tuda.stg.consys.logging.Logger;
import org.eclipse.jdt.internal.compiler.lookup.ReferenceBinding;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Map;

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

	public static final Map<String, Path[]> CASE_STUDIES = Maps.newHashMap();
	static {
		CASE_STUDIES.put("gcounter", Examples.GCOUNTER);
		CASE_STUDIES.put("pncounter", Examples.PNCOUNTER);
		CASE_STUDIES.put("gset", Examples.GSET);
		CASE_STUDIES.put("twophaseset", Examples.TWOPHASESET);
		CASE_STUDIES.put("credit_account", Examples.CREDIT_ACCOUNT);
		CASE_STUDIES.put("bank_account", Examples.BANK_ACCOUNT);
		CASE_STUDIES.put("bank_account_lww", Examples.BANK_ACCOUNT_LWW);
		CASE_STUDIES.put("joint_bank_account", Examples.JOINT_BANK_ACCOUNT);
		CASE_STUDIES.put("resettable_counter", Examples.RESETTABLE_COUNTER);
		CASE_STUDIES.put("consensus", Examples.CONSENSUS);
		CASE_STUDIES.put("distributed_lock", Examples.DISTRIBUTED_LOCK);
		CASE_STUDIES.put("tournament", Examples.TOURNAMENT);
		CASE_STUDIES.put("bounded_counter", Examples.BOUNDED_COUNTER);
		CASE_STUDIES.put("multi_value_register", Examples.MULTI_VALUE_REGISTER);
		CASE_STUDIES.put("add_only_graph", Examples.ADD_ONLY_GRAPH);
		CASE_STUDIES.put("two_phase_graph", Examples.TWO_PHASE_GRAPH);
		CASE_STUDIES.put("riak_gcounter", Examples.RIAK_GCOUNTER);
		CASE_STUDIES.put("riak_pncounter", Examples.RIAK_PNCOUNTER);
		CASE_STUDIES.put("riak_gset", Examples.RIAK_GSET);
		CASE_STUDIES.put("riak_twophaseset", Examples.RIAK_TWOPHASESET);
		CASE_STUDIES.put("riak_orset", Examples.RIAK_ORSET);
		//		CASE_STUDIES.put("shopping_cart", Examples.SHOPPING_CART);

	}

	private static final Path[] additionalLibraries = new Path[]{
			Paths.get("consys-invariants", "invariants-solver", "src", "main", "resources", "guava-14.0.1.jar"),
			Paths.get("consys-invariants", "invariants-solver", "src", "main", "resources", "checker-qual-3.27.0.jar"),
	};


	public static final Path[] DEFAULT_EXAMPLE = Examples.BOUNDED_COUNTER;

	private static void printUsage() {
		Logger.info("Usage: consys [--bench-sys | --bench-java | case-study-name | --count case-study-name]");
		Logger.info("Possible names: " + CASE_STUDIES.keySet());
	}

	private static void printErr(String message) {
		Logger.err(message);
		System.exit(-1);
	}

	private static Path[] parseCaseStudy(String name) {
		var result = CASE_STUDIES.getOrDefault(name.toLowerCase(), null);
		if (result == null) {
			printUsage();
			printErr("Expected case study name, but got " + name);
		}
		return result;
	}

	private enum ExecType {
		EXEC_SOLVER, BENCH_JAVA, BENCH_SYS, COUNT_COMPLEXITY
	}


	public static void main(String[] args) throws IOException {
		Path[] files = null;
		ExecType execType = ExecType.EXEC_SOLVER;

		if (args.length == 0) {
			//Default example
			files = DEFAULT_EXAMPLE;
		} else if (args.length == 1) {
			if (args[0].equals("--bench-sys")) {
				execType = ExecType.BENCH_SYS;
			} else if (args[0].equals("--bench-java")) {
				execType = ExecType.BENCH_JAVA;
			} else {
				files = parseCaseStudy(args[0]);
			}
		} else if (args.length == 2) {
			if (args[0].equals("--count")) {
				files = parseCaseStudy(args[1]);
				execType = ExecType.COUNT_COMPLEXITY;
			} else {
				printUsage();
				printErr("Expected --count as first argument, but got " + args[0]);
			}
		} else {
			printUsage();
			printErr("Expected 0 to 2 arguments, but got " + args.length);
		}

		if (execType == ExecType.EXEC_SOLVER) {

			ProgramConfig config = Examples.STATEFUL_CONFIG;
			var results = runChecker(config,
					/* libs */ additionalLibraries,
					/* checked classes */ files
			);

			for (var entry : results.entrySet()) {
				Logger.info("Result for " + String.valueOf(entry.getKey().shortReadableName()));
				Logger.withIdentation(() -> {
					Logger.info(entry.getValue().toString());
				});
			}
		} else if (execType == ExecType.COUNT_COMPLEXITY) {
			ProgramConfig config = Examples.STATEFUL_CONFIG;

			ProgramModel model =  createModel(config,
					/* libs */ additionalLibraries,
					/* checked classes */ files
			);


			var invariantComplexity = 0L;
			var preconditionComplexity = 0L;
			var postConditionComplexity = 0L;
			for (var entry : model.allClassConstraints()) {
				var className = String.valueOf(entry.getKey().sourceName);
				Logger.info("==============");
				Logger.info("class " + className);

				var inv =  entry.getValue().getInvariantComplexity();
				invariantComplexity += inv;
				var prec = entry.getValue().getPreconditionComplexity();
				preconditionComplexity += prec;
				var post = entry.getValue().getPostconditionComplexity();
				postConditionComplexity += post;

				Logger.info("invariant: " + inv);
				Logger.info("precondition: " + prec);
				Logger.info("postcondition: " + post);
			}

			Logger.info("==============");
			Logger.info("Total");
			Logger.info("invariant: " + invariantComplexity);
			Logger.info("precondition: " + preconditionComplexity);
			Logger.info("postcondition: " + postConditionComplexity);

		} else {
			Map<String, Double> results = null;

			if (execType == ExecType.BENCH_SYS) {
				results = CompilerBenchmark.runSysBench();
			} else if (execType == ExecType.BENCH_JAVA) {
				results = CompilerBenchmark.runJavaBench();
			} else {
				printErr("Unexpected benchmark type.");
			}

			for (var entry : results.entrySet()) {
				Logger.info(entry.getKey() + " = "  + (entry.getValue() / 1000000)   + "ms") ;
			}

		}

	}

	public static ProgramModel createModel(ProgramConfig config, Path[] additionalClasspath, Path[] sources) {
		// Compile the file to ASTs
		var compileResult = EclipseCompilerBinding.compile(additionalClasspath, sources);

		// Create the program model
		var model = new ProgramModel(compileResult, config);
		model.loadParsedClasses();
		return model;
	}

	public static Map<ReferenceBinding, ClassProperties.CheckResult> runChecker(ProgramConfig config, Path[] additionalClasspath, Path[] sources) {
		ProgramModel model = createModel(config, additionalClasspath, sources);

		// Check the classes
		return model.checkAll();
	}

}
