package de.tuda.stg.consys.invariants.subset.model;

import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.microsoft.z3.*;
import de.tuda.stg.consys.invariants.CompilerBinding;
import de.tuda.stg.consys.invariants.subset.*;
import de.tuda.stg.consys.invariants.subset.model.types.TypeModelFactory;
import org.eclipse.jdt.internal.compiler.lookup.CompilationUnitScope;
import org.eclipse.jdt.internal.compiler.lookup.ReferenceBinding;
import org.jmlspecs.jml4.ast.JmlTypeDeclaration;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

public class ProgramModel {
	static {
		loadZ3Libs();
	}

	private static void loadLib(Path lib) {
		Path libAbsolute = lib.toAbsolutePath();
		Logger.info("load lib: " + libAbsolute);
		System.load(libAbsolute.toString());
	}

	public static void loadZ3Libs() {
		// Set the correct lib folder
		Path libFolder = Paths.get("consys-invariants","lib");

		// Load the correct libs depending on OS
		String osname = System.getProperty("os.name").toLowerCase();
		if (osname.contains("mac")) {
			loadLib(libFolder.resolve("libz3.dylib"));
			loadLib(libFolder.resolve("libz3java.dylib"));
		} else if (osname.contains("linux")) {
			loadLib(libFolder.resolve("libz3.so"));
			loadLib(libFolder.resolve("libz3java.so"));
		} else {
			throw new RuntimeException("unsupported OS: " + osname);
		}
	}

	/* Possible solver tactics
	0 = "ackermannize_bv"
				1 = "subpaving"
				2 = "horn"
				3 = "horn-simplify"
				4 = "nlsat"
				5 = "qfnra-nlsat"
				6 = "nlqsat"
				7 = "qe-light"
				8 = "qe"
				9 = "qsat"
				10 = "qe2"
				11 = "qe_rec"
				12 = "psat"
				13 = "sat"
				14 = "sat-preprocess"
				15 = "ctx-solver-simplify"
				16 = "smt"
				17 = "psmt"
				18 = "unit-subsume-simplify"
				19 = "aig"
				20 = "add-bounds"
				21 = "card2bv"
				22 = "degree-shift"
				23 = "diff-neq"
				24 = "eq2bv"
				25 = "factor"
				26 = "fix-dl-var"
				27 = "fm"
				28 = "lia2card"
				29 = "lia2pb"
				30 = "nla2bv"
				31 = "normalize-bounds"
				32 = "pb2bv"
				33 = "propagate-ineqs"
				34 = "purify-arith"
				35 = "recover-01"
				36 = "bit-blast"
				37 = "bv1-blast"
				38 = "bv_bound_chk"
				39 = "propagate-bv-bounds"
				40 = "propagate-bv-bounds-new"
				41 = "reduce-bv-size"
				42 = "bvarray2uf"
				43 = "dt2bv"
				44 = "elim-small-bv"
				45 = "max-bv-sharing"
				46 = "blast-term-ite"
				47 = "cofactor-term-ite"
				48 = "collect-statistics"
				49 = "ctx-simplify"
				50 = "der"
				51 = "distribute-forall"
				52 = "dom-simplify"
				53 = "elim-term-ite"
				54 = "elim-uncnstr"
				55 = "injectivity"
				56 = "snf"
				57 = "nnf"
				58 = "occf"
				59 = "pb-preprocess"
				60 = "propagate-values"
				61 = "reduce-args"
				62 = "reduce-invertible"
				63 = "simplify"
				64 = "elim-and"
				65 = "solve-eqs"
				66 = "special-relations"
				67 = "split-clause"
				68 = "symmetry-reduce"
				69 = "tseitin-cnf"
				70 = "tseitin-cnf-core"
				71 = "qffd"
				72 = "pqffd"
				73 = "smtfd"
				74 = "fpa2bv"
				75 = "qffp"
				76 = "qffpbv"
				77 = "qffplra"
				78 = "default"
				79 = "sine-filter"
				80 = "qfbv-sls"
				81 = "nra"
				82 = "qfaufbv"
				83 = "qfauflia"
				84 = "qfbv"
				85 = "qfidl"
				86 = "qflia"
				87 = "qflra"
				88 = "qfnia"
				89 = "qfnra"
				90 = "qfuf"
				91 = "qfufbv"
				92 = "qfufbv_ackr"
				93 = "ufnia"
				94 = "uflra"
				95 = "auflia"
				96 = "auflira"
				97 = "aufnira"
				98 = "lra"
				99 = "lia"
				100 = "lira"
				101 = "skip"
				102 = "fail"
				103 = "fail-if-undecided"
				104 = "macro-finder"
				105 = "quasi-macros"
				106 = "ufbv-rewriter"
				107 = "bv"
				108 = "ufbv"
	 */


	public final Context ctx;
	public final Solver solver;

	public final ClassModelFactory classes;

	public final TypeModelFactory types;

	private final CompilerBinding.CompileResult compileResult;

	// Stores all class models
	private final Map<ReferenceBinding, BaseClassModel> models;
	// Stores the sequence in which the models have been added.
	private final List<ReferenceBinding> modelSequence;

	public ProgramModel(Context ctx, CompilerBinding.CompileResult compileResult) {
		this.ctx = ctx;
		this.solver =  ctx.mkSolver(); // ctx.mkSolver(ctx.mkTactic("default"));

//		var params = ctx.mkParams();
//		params.add("max_degree", 128);
//		params.add("blast_full", true);
//		params.add("array.weak", true);
//		params.add("enable_pre_simplify", true);
//		solver.setParameters(params);

		this.compileResult = compileResult;
		this.types = new TypeModelFactory(this);
		this.classes = new ClassModelFactory(this);

		this.models = Maps.newHashMap();
		this.modelSequence = Lists.newLinkedList();
	}

	public ProgramModel(CompilerBinding.CompileResult compileResult) {
		this(
				new Context(
					/*Map.of("model", "true",
					"proof", "true",
					"auto-config", "false")*/
				),
				compileResult);
	}

	public Optional<BaseClassModel> getModelForClass(ReferenceBinding refBinding) {
		return Optional.ofNullable(models.getOrDefault(refBinding, null));
	}

	public void checkAll() {
		Logger.info("checking data model " + modelSequence.stream().map(binding -> String.valueOf(binding.shortReadableName())).collect(Collectors.toUnmodifiableList()));

		for (var binding : modelSequence) {
			Logger.info("class " + String.valueOf(binding.shortReadableName()));
			Logger.withIdentation(() -> {
				// Parse the z3 model from AST.
				BaseClassModel classModel = models.get(binding);
				ClassProperties.CheckResult result;
				if (classModel instanceof ReplicatedClassModel) {
					Logger.info("@ReplicatedModel");
					var constraints = new ReplicatedClassConstraints<>(this, (ReplicatedClassModel) classModel);
					var properties = new ReplicatedClassProperties<>(this, constraints);
					result = properties.check();
				} else {
					Logger.info("@DataModel");
					var constraints = new BaseClassConstraints<>(this, classModel);
					var properties = new BaseClassProperties<>(this, constraints);
					result = properties.check();
				}
				Logger.info("Result for class " + String.valueOf(binding.shortReadableName()));
				Logger.withIdentation(() -> {
					Logger.info(result.toString());
				});
			});

		}
	}

	// Loads the parsed classes into this program model.
	public void loadParsedClasses() {
		List<JmlTypeDeclaration> declarations = compileResult.getTypes();

		classes.generateModelForClasses(declarations, (jmlType, classModel) -> {
			models.put(jmlType.binding, classModel);
			modelSequence.add(jmlType.binding);
		});
	}

	public CompilationUnitScope getParserScope() {
		return compileResult.getParser().compilationUnit.scope;
	}


}
