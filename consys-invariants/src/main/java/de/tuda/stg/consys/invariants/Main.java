package de.tuda.stg.consys.invariants;

import com.microsoft.z3.Context;
import de.tuda.stg.consys.invariants.subset.PropertyModel;
import de.tuda.stg.consys.invariants.subset.model.ConstraintModel;
import de.tuda.stg.consys.invariants.subset.model.ClassModel;
import org.eclipse.jdt.core.compiler.CompilationProgress;
import org.eclipse.jdt.internal.compiler.ast.TypeDeclaration;
import org.jmlspecs.jml4.ast.JmlTypeDeclaration;
import de.tuda.stg.consys.invariants.subset.Z3Checker;
import de.tuda.stg.consys.invariants.subset.visitors.ModelGenerator;

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

  public static void main(String[] args) {
    // Set the source file
    Path[] sources = new Path[] {
            Paths.get("consys-invariants", "InvariantExamples", "BankAccountCRDT", "BankAccountCRDT.java")
    };

    // Compile the file to ASTs
    CompilerBinding compiler = new CompilerBinding();
    TypeDeclaration[] declarations = compiler.compile(sources);

    // Run the property checker given the class ASTs
    CheckerBinding checker = new CheckerBinding();
    for (TypeDeclaration clazz : declarations) {
      if (!(clazz instanceof JmlTypeDeclaration)) {
        throw new IllegalArgumentException("class is not a Jml type.");
      }
      checker.check((JmlTypeDeclaration) clazz);
    }
  }


}
