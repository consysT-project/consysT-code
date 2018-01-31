package tests;

import org.checkerframework.framework.test.CheckerFrameworkPerFileTest;
import org.junit.runners.Parameterized.Parameters;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class ConsistencyTest extends CheckerFrameworkPerFileTest {

    public ConsistencyTest(File file) {
        super(
                file,
                com.github.allprojects.consistencyTypes.ConsistencyChecker.class,
                "consistency",
                "-Anomsgtext");
    }

    @Parameters
    public static List<File> getTestFiles() {
        String consistencyChecker = System.getProperties().getProperty("consistencyChecker");
        System.out.println(consistencyChecker);
        File dir = new File (consistencyChecker + "consistencyCheckerTest/consistency");
        List<File> files = new ArrayList<File>();
        files.addAll(Arrays.asList(dir.listFiles()));
        return files;
    }
}
