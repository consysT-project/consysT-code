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
		this.solver = ctx.mkSolver();
		this.compileResult = compileResult;
		this.types = new TypeModelFactory(this);
		this.classes = new ClassModelFactory(this);

		this.models = Maps.newHashMap();
		this.modelSequence = Lists.newLinkedList();
	}

	public ProgramModel(CompilerBinding.CompileResult compileResult) {
		this(new Context(), compileResult);
	}

	public void addClass(JmlTypeDeclaration jmlClass) {
		classes.generateModelFor(jmlClass).ifPresent(clazzModel -> {
			models.put(jmlClass.binding, clazzModel);
			modelSequence.add(jmlClass.binding);
		});
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

				if (classModel instanceof ReplicatedClassModel) {
					Logger.info("@ReplicatedModel");
					var constraints = new ReplicatedClassConstraints<>(this, (ReplicatedClassModel) classModel);
					var properties = new ReplicatedClassProperties<>(this, constraints);
					var result = properties.check();
					Logger.info(result.toString());
				} else {
					Logger.info("@DataModel");
					var constraints = new BaseClassConstraints<>(this, classModel);
					var properties = new BaseClassProperties<>(this, constraints);
					var result = properties.check();
					Logger.info(result.toString());
				}
			});

		}
	}

	// Loads the parsed classes into this program model.
	public void loadParsedClasses() {
		List<JmlTypeDeclaration> declarations = compileResult.getTypes();
		for (var clazz : declarations) {
			addClass(clazz);
		}
	}

	public CompilationUnitScope getParserScope() {
		return compileResult.getParser().compilationUnit.scope;
	}

	public boolean isValid(Expr<BoolSort> expr) {
		Status status = solver.check(ctx.mkNot(expr));
		switch (status) {
			case UNSATISFIABLE:
				return true;
			case SATISFIABLE:
				//System.out.println(expr);
				//System.out.println(solver.getModel());
				return false;
			case UNKNOWN:
				throw new RuntimeException("z3 was not able to solve the following expression:\n" + expr);
			default:
				//Does not exist
				throw new RuntimeException();
		}
	}
}
