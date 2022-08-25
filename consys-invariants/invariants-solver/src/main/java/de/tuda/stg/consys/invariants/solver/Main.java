package de.tuda.stg.consys.invariants.solver;

import de.tuda.stg.consys.invariants.solver.subset.ProgramConfig;
import de.tuda.stg.consys.invariants.solver.subset.model.ProgramModel;

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

    runChecker(config,
            /* libs */ new Path[] { Paths.get("consys-invariants", "invariants-solver", "src", "main", "resources", "guava-14.0.1.jar") },
            /* checked classes */ Examples.IMMUTABLE_CRDTLIB
    );
  }

  public static void runChecker(ProgramConfig config, Path[] additionalClasspath, Path[] sources) {
    // Compile the file to ASTs
    var compileResult = EclipseCompilerBinding.compile(additionalClasspath, sources);

    // Create the program model
    var model = new ProgramModel(compileResult, config);
    model.loadParsedClasses();

    // Check the classes
    model.checkAll();
  }


}
