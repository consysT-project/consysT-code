package de.tuda.stg.consys.invariants;

import com.microsoft.z3.Context;
import de.tuda.stg.consys.invariants.subset.ClassProperties;
import de.tuda.stg.consys.invariants.subset.model.ClassModel;
import de.tuda.stg.consys.invariants.subset.ClassConstraints;
import org.jmlspecs.jml4.ast.JmlTypeDeclaration;

import java.nio.file.Path;
import java.nio.file.Paths;

/**
 * Created on 23.06.21.
 *
 * @author Mirko Köhler
 */
public class CheckerBinding {
    static {
        loadZ3Libs();
    }

    private final Context ctx;

    public CheckerBinding() {
        this.ctx = new Context();
    }

    public static void loadLib(Path lib) {
        Path libAbsolute = lib.toAbsolutePath();
        System.out.println("load lib: " + libAbsolute);
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



    public void check(JmlTypeDeclaration jmlClass) {
        // Parse the z3 model from AST.
        ClassModel model = new ClassModel(ctx, jmlClass);
        ClassConstraints constraints = new ClassConstraints(ctx, model);

        System.out.println(constraints);

        // Check the properties
        ClassProperties properties = new ClassProperties(ctx, constraints);
        System.out.println("--- Class properties for " + model.getClassName());
        System.out.println("initial satisfies invariant: " + properties.checkInitialSatisfiesInvariant());
        System.out.println("initial satisfies mergability: " + properties.checkInitialSatisfiesMergability());
        System.out.println("---");
        System.out.println("merge satisfies invariant: " + properties.checkMergeSatisfiesInvariant());
        System.out.println("merge satisfies mergability: " + properties.checkMergeSatisfiesMergability());
        System.out.println("---");
        model.getMethods().forEach(m -> {
            System.out.println("- for method " + m);

            boolean r1 = properties.checkMethodSatisfiesInvariant(m.getBinding());
            System.out.println("  satisfies invariant: " + r1);

            boolean r2 = properties.checkMethodSatisfiesMergability(m.getBinding());
            System.out.println("  satisfies mergability: " + r2);
        });
    }
}
