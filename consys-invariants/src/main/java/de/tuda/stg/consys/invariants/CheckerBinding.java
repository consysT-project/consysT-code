package de.tuda.stg.consys.invariants;

import com.microsoft.z3.Context;
import de.tuda.stg.consys.invariants.subset.PropertyModel;
import de.tuda.stg.consys.invariants.subset.model.ClassModel;
import de.tuda.stg.consys.invariants.subset.model.ConstraintModel;
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
        ClassModel scope = new ClassModel(ctx, jmlClass);
        ConstraintModel model = new ConstraintModel(ctx, scope);

        System.out.println(model);

        // Check the properties
        PropertyModel property = new PropertyModel(ctx, model);
        scope.getMethods().forEach(m -> {
            boolean r1 = property.checkInvariantSufficiency(m.getBinding());
            System.out.println("[InvSuff] " + m + ": " + r1);

            boolean r3 = property.checkConcurrentStateMerge(m.getBinding());
            System.out.println("[Concurrent] " + m + ": " + r3);

            boolean r4 = property.checkConcurrentStateMerge2(m.getBinding());
            System.out.println("[Concurrent2] " + m + ": " + r4);
        });

        boolean r2 = property.checkInvariantSufficientMerge();
        System.out.println("[MergeSuff] " + r2);

//          boolean r2 = property.checkMergeIdempotency();
//          System.out.println("[MergeIdem] " + r2);


//          clazz.traverse(generator, clazz.scope);
//          // visit class as JmlTypeDeclaration explicitly to get the invariant
//          // otherwise, only fields and methods would be added without getting the invariant
//          generator.visit((JmlTypeDeclaration) clazz, clazz.scope);
//          InternalClass result = generator.getResult();
//
//          // check if sequential execution and the must have properties of the merge function hold
//          System.out.println("Prerequisities okay?: " + Z3Checker.checkPreRequisities(result));
//
//          // check if weak consistency is applicable to all methods
//          System.out.println(
//              "Weak consistency possible for all methods?: "
//                  + Z3Checker.checkWeakConsistencyForMethods(result));
//
//          // reset visitor to prepare for the next class
//          generator.reset();
    }
}
