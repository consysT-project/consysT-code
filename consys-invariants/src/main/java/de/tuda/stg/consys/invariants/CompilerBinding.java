package de.tuda.stg.consys.invariants;

import org.eclipse.jdt.core.compiler.CompilationProgress;
import org.eclipse.jdt.internal.compiler.ast.TypeDeclaration;
import org.eclipse.jdt.internal.compiler.batch.Main;

import java.io.PrintWriter;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Map;

/**
 * Created on 23.06.21.
 *
 * @author Mirko Köhler
 */
public class CompilerBinding {

    private final org.eclipse.jdt.internal.compiler.batch.Main compilerStarter;

    public CompilerBinding() {
        this.compilerStarter = new org.eclipse.jdt.internal.compiler.batch.Main(
                new PrintWriter(System.out),
                new PrintWriter(System.err),
                false,
                (Map) null,
                (CompilationProgress) null);
    }


    public TypeDeclaration[] compile(Path... sourceFiles) {

        String[] sourceFileStrings = Arrays.stream(sourceFiles)
                .map(Path::toString)
                .toArray(String[]::new);

        System.out.println("Compiling files: " + Arrays.toString(sourceFileStrings));
        compilerStarter.compile(sourceFileStrings);

        // ensure that compilation was successful -> types array contains class definitions
        if(compilerStarter.batchCompiler.parser.compilationUnit.types == null) {
            throw new IllegalStateException("compiler was not able to generate types from the given source files.");
        }

        return compilerStarter.batchCompiler.parser.compilationUnit.types;
    }


}
