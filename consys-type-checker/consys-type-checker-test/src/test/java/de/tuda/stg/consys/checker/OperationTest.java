package de.tuda.stg.consys.checker;

import org.checkerframework.framework.test.CheckerFrameworkPerFileTest;
import org.junit.runners.Parameterized;

import java.io.File;

public class OperationTest extends CheckerFrameworkPerFileTest {

    public OperationTest(File file) {
        super(
                file,
                ConsistencyChecker.class,
                "testfiles/operations",
                //Mandated by the checker framework
                "-Anomsgtext",
                //Disable warnings, so that the tests do not fail when there is the warning about using the unannotated jdk
                "-nowarn",
                "-Alint=disableSubChecker");
    }

    @Parameterized.Parameters
    public static String[] getTestDirs() {
        return new String[] {"testfiles/operations"};
    }
}
