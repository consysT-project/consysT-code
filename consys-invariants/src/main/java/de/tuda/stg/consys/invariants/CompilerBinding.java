package de.tuda.stg.consys.invariants;

import com.google.common.collect.Lists;
import de.tuda.stg.consys.invariants.subset.Logger;
import org.eclipse.jdt.core.compiler.CharOperation;
import org.eclipse.jdt.core.compiler.CompilationProgress;
import org.eclipse.jdt.core.compiler.InvalidInputException;
import org.eclipse.jdt.internal.compiler.Compiler;
import org.eclipse.jdt.internal.compiler.*;
import org.eclipse.jdt.internal.compiler.ast.CompilationUnitDeclaration;
import org.eclipse.jdt.internal.compiler.batch.FileSystem;
import org.eclipse.jdt.internal.compiler.batch.Main;
import org.eclipse.jdt.internal.compiler.env.ICompilationUnit;
import org.eclipse.jdt.internal.compiler.env.INameEnvironment;
import org.eclipse.jdt.internal.compiler.impl.CompilerOptions;
import org.eclipse.jdt.internal.compiler.lookup.LookupEnvironment;
import org.eclipse.jdt.internal.compiler.lookup.ReferenceBinding;
import org.eclipse.jdt.internal.compiler.parser.Parser;
import org.eclipse.jdt.internal.compiler.problem.ProblemReporter;
import org.jmlspecs.jml4.ast.JmlTypeDeclaration;

import java.io.File;
import java.io.PrintWriter;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;

/**
 * Created on 23.06.21.
 *
 * @author Mirko Köhler
 */
public class CompilerBinding {

    private CompilerBinding() { }

    public static CompileResult compile(Path... sourceFiles) {

        var compilerStarter = new ConsysCompilerStarter(
                Logger.info,
                Logger.warn,
                false,
                (Map) null,
                (CompilationProgress) null);

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

        return compilerStarter.getResult();
    }

    private static class ConsysCompilerStarter extends Main {

        private final CompileResult result;

        public ConsysCompilerStarter(PrintWriter outWriter, PrintWriter errWriter, boolean systemExitWhenFinished, Map customDefaultOptions, CompilationProgress compilationProgress) {
            super(outWriter, errWriter, systemExitWhenFinished, customDefaultOptions, compilationProgress);
            result = new CompileResult(this);
        }

//        @Override
//        public ICompilerRequestor getBatchRequestor() {
//            var superRequestor = super.getBatchRequestor();
//            return new ICompilerRequestor() {
//                @Override
//                public void acceptResult(CompilationResult compileResult) {
////                    var compilationUnitTypes = batchCompiler.parser.compilationUnit.types;
////                    for (var type : compilationUnitTypes) {
////                        result.addJmlTypeDeclaration((JmlTypeDeclaration) type);
////                    }
//                    superRequestor.acceptResult(compileResult);
//                }
//            };
//        }

        @Override
        /* copied from parent and slightly changed */
        public void performCompilation() throws InvalidInputException {
            this.startTime = System.currentTimeMillis();
            FileSystem environment = this.getLibraryAccess();
            this.compilerOptions = new CompilerOptions(this.options);
            this.compilerOptions.performMethodsFullRecovery = false;
            this.compilerOptions.performStatementsRecovery = false;

            /* Initialize to Consys compiler */
            this.batchCompiler = new ConsysCompiler(environment, this.getHandlingPolicy(), this.compilerOptions, this.getBatchRequestor(), this.getProblemFactory(), this.out, this.progress);
            /* The rest is the same as parent */

            this.batchCompiler.remainingIterations = this.maxRepetition - this.currentRepetition;
            String setting = System.getProperty("jdt.compiler.useSingleThread");
            this.batchCompiler.useSingleThread = setting != null && setting.equals("true");
            if (this.compilerOptions.complianceLevel >= 3276800L && this.compilerOptions.processAnnotations) {
                if (this.checkVMVersion(3276800L)) {
                    this.initializeAnnotationProcessorManager();
                    if (this.classNames != null) {
                        this.batchCompiler.setBinaryTypes(this.processClassNames(this.batchCompiler.lookupEnvironment));
                    }
                } else {
                    this.logger.logIncorrectVMVersionForAnnotationProcessing();
                }
            }

            this.compilerOptions.verbose = this.verbose;
            this.compilerOptions.produceReferenceInfo = this.produceRefInfo;

            try {
                this.logger.startLoggingSources();
                this.batchCompiler.compile(this.getCompilationUnits());
            } finally {
                this.logger.endLoggingSources();
            }

            //TODO: Is this important?
//            if (this.extraProblems != null) {
//                this.logger.loggingExtraProblems(this);
//                this.extraProblems = null;
//            }

            if (this.compilerStats != null) {
                this.compilerStats[this.currentRepetition] = this.batchCompiler.stats;
            }

            this.logger.printStats();
            environment.cleanup();
        }

        /* private method copied from parent */
        private boolean checkVMVersion(long minimalSupportedVersion) {
            String classFileVersion = System.getProperty("java.class.version");
            if (classFileVersion == null) {
                return false;
            } else {
                int index = classFileVersion.indexOf(46);
                if (index == -1) {
                    return false;
                } else {
                    int majorVersion;
                    try {
                        majorVersion = Integer.parseInt(classFileVersion.substring(0, index));
                    } catch (NumberFormatException var7) {
                        return false;
                    }

                    switch(majorVersion) {
                        case 45:
                            if (2949123L >= minimalSupportedVersion) {
                                return true;
                            }

                            return false;
                        case 46:
                            if (3014656L >= minimalSupportedVersion) {
                                return true;
                            }

                            return false;
                        case 47:
                            if (3080192L >= minimalSupportedVersion) {
                                return true;
                            }

                            return false;
                        case 48:
                            if (3145728L >= minimalSupportedVersion) {
                                return true;
                            }

                            return false;
                        case 49:
                            if (3211264L >= minimalSupportedVersion) {
                                return true;
                            }

                            return false;
                        case 50:
                            if (3276800L >= minimalSupportedVersion) {
                                return true;
                            }

                            return false;
                        case 51:
                            if (3342336L >= minimalSupportedVersion) {
                                return true;
                            }

                            return false;
                        default:
                            return false;
                    }
                }
            }
        }

        /* private source copied from parent */
        private ReferenceBinding[] processClassNames(LookupEnvironment environment) throws InvalidInputException {
            int length = this.classNames.length;
            ReferenceBinding[] referenceBindings = new ReferenceBinding[length];

            for(int i = 0; i < length; ++i) {
                String currentName = this.classNames[i];
                char[][] compoundName = null;
                if (currentName.indexOf(46) != -1) {
                    char[] typeName = currentName.toCharArray();
                    compoundName = CharOperation.splitOn('.', typeName);
                } else {
                    compoundName = new char[][]{currentName.toCharArray()};
                }

                ReferenceBinding type = environment.getType(compoundName);
                if (type == null || !type.isValidBinding()) {
                    throw new InvalidInputException(this.bind("configure.invalidClassName", currentName));
                }

                if (type.isBinaryBinding()) {
                    referenceBindings[i] = type;
                }
            }

            return referenceBindings;
        }

        public CompileResult getResult() {
            return result;
        }


        private class ConsysCompiler extends Compiler {
            public ConsysCompiler(INameEnvironment environment, IErrorHandlingPolicy policy, CompilerOptions options, ICompilerRequestor requestor, IProblemFactory problemFactory, PrintWriter out, CompilationProgress progress) {
                super(environment, policy, options, requestor, problemFactory, out, progress);
            }

            @Override
            public void initializeParser() {
                /* Initialize to ConsysParser */
                this.parser = new ConsysParser(this.problemReporter, this.options.parseLiteralExpressionsAsConstants);
            }


            private class ConsysParser extends Parser {

                public ConsysParser(ProblemReporter problemReporter, boolean optimizeStringLiterals) {
                    super(problemReporter, optimizeStringLiterals);
                }

                @Override
                public CompilationUnitDeclaration parse(ICompilationUnit sourceUnit, CompilationResult compilationResult) {
                    var declaration = super.parse(sourceUnit, compilationResult);
                    for (var type : declaration.types) {
                        result.addJmlTypeDeclaration((JmlTypeDeclaration) type);
                    }
                    return declaration;
                }


            }
        }
    }



    public static class CompileResult {
        private final Main compilerStarter;
        private final List<JmlTypeDeclaration> parsedTypes = Lists.newLinkedList();

        public CompileResult(Main compilerStarter) {
            this.compilerStarter = compilerStarter;
        }

        void addJmlTypeDeclaration(JmlTypeDeclaration type) {
            parsedTypes.add(type);
        }

        public List<JmlTypeDeclaration> getTypes() {
            return Collections.unmodifiableList(parsedTypes);
        }

        public Parser getParser() {
            return compilerStarter.batchCompiler.parser;
        }
    }


}
