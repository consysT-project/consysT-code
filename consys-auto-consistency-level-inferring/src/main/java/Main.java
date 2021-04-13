import org.eclipse.jdt.core.compiler.CompilationProgress;
import org.eclipse.jdt.internal.compiler.ast.TypeDeclaration;
import org.jmlspecs.jml4.ast.JmlTypeDeclaration;
import subset.Z3Checker;
import subset.visitors.ModelGenerator;
import subset.z3_model.InternalClass;

import java.io.PrintWriter;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
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

  /**
   * compilation results of class declarations
   */
  public static TypeDeclaration[] classDeclarations = null;

  private static void loadLib(String libname) {
    Path lib = Paths.get("consys-auto-consistency-level-inferring","lib",libname).toAbsolutePath();
    System.out.println("load " + libname + ": " + lib);
    Runtime.getRuntime().load(lib.toString());
  }

  /**
   * Starting point of program
   *
   * @param args used provide the path to the java file
   */
  public static void main(String[] args) {

    // Load z3 libraries from lib folder
    String osname = System.getProperty("os.name").toLowerCase();
    // Load the correct libs depending on OS
    if (osname.contains("mac")) {
      loadLib("libz3.dylib");
      loadLib("libz3java.dylib");
    } else if (osname.contains("linux")) {
      loadLib("libz3.so");
      loadLib("libz3java.so");
    } else {
      throw new RuntimeException("Unsupported OS: " + osname);
    }

    // Set the source file
    Path sourcePath = Paths.get("consys-auto-consistency-level-inferring", "src", "main", "resources", "test", "Counter.java");
    System.out.println("compiling: " + sourcePath.toString());


    // compile Java + JML using JML4 compiler plugin
    org.eclipse.jdt.internal.compiler.batch.Main compilerStarter =
        new org.eclipse.jdt.internal.compiler.batch.Main(
            new PrintWriter(System.out),
            new PrintWriter(System.err),
            false,
            (Map) null,
            (CompilationProgress) null);

    compilerStarter.compile(new String[] { sourcePath.toString() });

    // ensure that compilation was successful -> types array contains class definitions
    if (compilerStarter.batchCompiler.parser.compilationUnit.types != null) {
      classDeclarations = compilerStarter.batchCompiler.parser.compilationUnit.types;

      /*
       ************************************* Analysis Steps ************************************
       */

      /* Visit compiled class definition and build internal data structure with translation of JML
      formulas to SMT formulas */
      ModelGenerator generator = new ModelGenerator();
      for (TypeDeclaration clazz : classDeclarations) {
        if (clazz instanceof JmlTypeDeclaration) {
          clazz.traverse(generator, clazz.scope);
          // visit class as JmlTypeDeclaration explicitly to get the invariant
          // otherwise, only fields and methods would be added without getting the invariant
          generator.visit((JmlTypeDeclaration) clazz, clazz.scope);
          InternalClass result = generator.getResult();

          // check if sequential execution and the must have properties of the merge function hold
          System.out.println("Prerequisities okay?: " + Z3Checker.checkPreRequisities(result));

          // check if weak consistency is applicable to all methods
          System.out.println(
              "Weak consistency possible for all methods?: "
                  + Z3Checker.checkWeakConsistencyForMethods(result));

          // reset visitor to prepare for the next class
          generator.reset();
        } else {
          System.out.println(
              "Type " + Arrays.toString(clazz.name) + " does not contain JML annotations");
        }
      }

    } else {
      System.out.println("No class definitions could be found");
      System.exit(-1);
    }
  }
}
