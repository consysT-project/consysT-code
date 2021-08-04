package de.tuda.stg.consys.invariants;

import de.tuda.stg.consys.invariants.subset.Logger;
import org.eclipse.jdt.core.compiler.CompilationProgress;
import org.eclipse.jdt.internal.compiler.parser.Parser;

import java.io.File;
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


    public Parser compile(Path... sourceFiles) {

        String[] sourceFileStrings = Arrays.stream(sourceFiles)
                .map(Path::toString)
                .toArray(String[]::new);

        Path[] classPath = new Path[] {
                // The java library
                Paths.get("consys-invariants","src", "main", "resources", "rt.jar"),
                // ConSysT annotations
                Paths.get("consys-annotations", "target", "consys-annotations-3.0.0-alpha.jar")
        };


        String[] compilerOpts = new String[] {
                "-cp", Arrays.stream(classPath).map(Path::toString).reduce( (acc, e) -> acc + File.pathSeparator + e).orElse(".")
        };

        String[] argv = new String[sourceFileStrings.length + compilerOpts.length];
        System.arraycopy(sourceFileStrings, 0, argv, 0, sourceFileStrings.length);
        System.arraycopy(compilerOpts, 0, argv, sourceFileStrings.length, compilerOpts.length);

        Logger.info("exec javac with argv: " + Arrays.toString(argv));
        compilerStarter.compile(argv);

        // ensure that compilation was successful -> types array contains class definitions
        if(compilerStarter.batchCompiler.parser.compilationUnit.types == null) {
            throw new IllegalStateException("compiler was not able to generate types from the given source files.");
        }

        return compilerStarter.batchCompiler.parser;
    }


}
