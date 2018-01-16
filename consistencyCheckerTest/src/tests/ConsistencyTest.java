package tests;

import org.checkerframework.framework.test.CheckerFrameworkPerDirectoryTest;
import org.junit.runners.Parameterized.Parameters;

import java.io.File;
import java.util.List;

public class ConsistencyTest extends CheckerFrameworkPerDirectoryTest {

    public ConsistencyTest(List<File> testFiles) {
        super(
                testFiles,
                com.github.allprojects.consistencyTypes.ConsistencyChecker.class,
                "consistency",
                "-Anomsgtext");
    }

    @Parameters
    public static String[] getTestDirs() {
        return new String[] {"consistency", "all-systems"};
    }
}
