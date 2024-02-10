package de.tuda.stg.consys.checker;

import org.checkerframework.framework.test.CheckerFrameworkPerFileTest;
import org.junit.runners.Parameterized;

import java.io.File;

public class BasicsTest extends CheckerFrameworkPerFileTest {

    public BasicsTest(File file) {
        super(
                file,
                ConsistencyChecker.class,
                "testfiles/basics",
                //Mandated by the checker framework
                "-Anomsgtext",
                //Disable warnings, so that the tests do not fail when there is the warning about using the unannotated jdk
                "-nowarn",
                "-AcheckPurityAnnotations",
                "-AsuppressWarnings=inconsistent.constructor.type");
    }

    @Parameterized.Parameters
    public static String[] getTestDirs() {
        return new String[] {"testfiles/basics"};
    }
}
