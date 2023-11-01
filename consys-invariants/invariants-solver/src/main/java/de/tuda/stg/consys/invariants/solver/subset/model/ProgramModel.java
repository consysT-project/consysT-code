package de.tuda.stg.consys.invariants.solver.subset.model;

import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.microsoft.z3.Context;
import com.microsoft.z3.Solver;
import de.tuda.stg.consys.invariants.solver.EclipseCompilerBinding;
import de.tuda.stg.consys.invariants.solver.subset.BaseClassProperties;
import de.tuda.stg.consys.invariants.solver.subset.ClassProperties;
import de.tuda.stg.consys.invariants.solver.subset.ProgramConfig;
import de.tuda.stg.consys.invariants.solver.subset.ReplicatedClassProperties;
import de.tuda.stg.consys.invariants.solver.subset.constraints.BaseClassConstraints;
import de.tuda.stg.consys.invariants.solver.subset.constraints.ReplicatedClassConstraints;
import de.tuda.stg.consys.invariants.solver.subset.model.types.TypeModelFactory;
import de.tuda.stg.consys.invariants.solver.subset.utils.JDTUtils;
import de.tuda.stg.consys.logging.Logger;
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
		Path libFolder = Paths.get("consys-invariants", "invariants-solver", "lib");

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

	public final TypeModelFactory types;

	private final EclipseCompilerBinding.CompileResult compileResult;

	public final ProgramConfig config;

	// Stores all class models
	private final Map<ReferenceBinding, BaseClassModel> models;
	// Stores all class properties
	private final Map<ReferenceBinding, BaseClassConstraints<?>> constraints;

	// Stores the sequence in which the models have been added.
	private final List<ReferenceBinding> modelSequence;

	public ProgramModel(Context ctx, EclipseCompilerBinding.CompileResult compileResult, ProgramConfig config) {
		this.ctx = ctx;
		this.solver =  ctx.mkSolver();
//			ctx.mkSolver(ctx.mkTactic("default"));
		this.config = config;

		var params = ctx.mkParams();
		params.add("enable_pre_simplify", true);
		solver.setParameters(params);

		this.compileResult = compileResult;
		this.types = new TypeModelFactory(this);

		this.models = Maps.newHashMap();
		this.constraints = Maps.newHashMap();
		this.modelSequence = Lists.newLinkedList();
	}

	public ProgramModel(EclipseCompilerBinding.CompileResult compileResult, ProgramConfig config) {
		this(
				new Context(
					/*Map.of("model", "true",
					"proof", "true",
					"auto-config", "false")*/
				),
				compileResult, config);
	}

	public Iterable<Map.Entry<ReferenceBinding, BaseClassConstraints<?>>> allClassConstraints() {
		return constraints.entrySet();
	}

	public Optional<BaseClassModel> getClassModel(ReferenceBinding refBinding) {
		return Optional.ofNullable(models.getOrDefault(JDTUtils.erase(refBinding), null));
	}

	public Optional<BaseClassConstraints<?>> getClassConstraints(ReferenceBinding refBinding) {
		return Optional.ofNullable(constraints.getOrDefault(JDTUtils.erase(refBinding), null));
	}

	public Map<ReferenceBinding, ClassProperties.CheckResult> checkAll() {
		Logger.info("Checking classes " + modelSequence.stream().map(binding -> String.valueOf(binding.shortReadableName())).collect(Collectors.toUnmodifiableList()));

		Map<ReferenceBinding, ClassProperties.CheckResult> results = Maps.newHashMap();

		for (var binding : modelSequence) {
			Logger.info("Verifying " + String.valueOf(binding.shortReadableName()));
			Logger.withIdentation(() -> {
				// Parse the z3 model from AST.
				BaseClassModel classModel = models.get(binding);
				ClassProperties.CheckResult result;
				if (classModel instanceof ReplicatedClassModel) {
					var constraint = constraints.get(classModel.getBinding());
					var properties = new ReplicatedClassProperties(this, (ReplicatedClassConstraints) constraint);
					result = properties.check(null);
				} else {
					var constraint = constraints.get(classModel.getBinding());
					var properties = new BaseClassProperties<>(this, constraint);
					result = properties.check(null);
				}

				results.put(binding, result);
			});
		}

		Logger.info("Done.");

		return results;
	}

	private static String classModelTypeName(BaseClassModel classModel) {
		if (classModel instanceof ReplicatedClassModel)
			return "@ReplicatedModel";
		 else
			return "@DataModel";
	}

	// Loads the parsed classes into this program model.
	public void loadParsedClasses() {
		List<JmlTypeDeclaration> declarations = compileResult.getTypes();
		List<BaseClassModel> generatedModels = Lists.newLinkedList();

		/* Create class models */
		for (var jmlType : declarations) {
			if (jmlType.annotations != null) {
				var hasDataModelAnnotation = Arrays.stream(jmlType.annotations)
						.anyMatch(anno -> JDTUtils.typeIsTypeOfName(anno.resolvedType, "de.tuda.stg.consys.annotations.invariants.DataModel"));
				var hasReplicatedModelAnnotation = Arrays.stream(jmlType.annotations)
						.anyMatch(anno -> JDTUtils.typeIsTypeOfName(anno.resolvedType, "de.tuda.stg.consys.annotations.invariants.ReplicatedModel"));

				BaseClassModel classModel = null;

				if (hasDataModelAnnotation) {
					classModel = new BaseClassModel(this, jmlType, false);
				} else if (hasReplicatedModelAnnotation) {
					classModel = new ReplicatedClassModel(this, jmlType, false);
				}

				if (classModel != null) {
					generatedModels.add(classModel);
					continue;
				}
			}
			Logger.warn("class is not part of the constraints model: " + String.valueOf(jmlType.name));
		}

		for (var classModel : generatedModels) {
			classModel.initializeFields();
			classModel.initializeSort();
			models.put(JDTUtils.erase(classModel.getBinding()), classModel);
			modelSequence.add(JDTUtils.erase(classModel.getBinding()));
		}

		for (var classModel : generatedModels) {
			classModel.initializeMethods();
		}

		/* Create class properties */
		for (var classModel : generatedModels) {
			// Parse the z3 model from AST.
			if (classModel instanceof ReplicatedClassModel) {
				var constraint = new ReplicatedClassConstraints<>(this, (ReplicatedClassModel) classModel);
				constraints.put(JDTUtils.erase(classModel.getBinding()), constraint);
			} else {
				var constraint = new BaseClassConstraints<>(this, classModel);
				constraints.put(JDTUtils.erase(classModel.getBinding()), constraint);
			}
		}
	}

	private CompilationUnitScope getParserScope() {
		//TODO: Can we change this to take the correct compilation unit?
		return compileResult.getParser().compilationUnit.scope;
	}

	public ReferenceBinding bindingForJavaLangObject() {
		return  getParserScope().getJavaLangObject();
	}



}
