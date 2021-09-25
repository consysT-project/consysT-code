package de.tuda.stg.consys.checker;

import org.checkerframework.framework.test.CheckerFrameworkPerDirectoryTest;
import org.junit.runners.Parameterized;

import java.io.File;
import java.util.List;

public class DirectoryTest extends CheckerFrameworkPerDirectoryTest {

    public DirectoryTest(List<File> testFiles) {
        super(
                testFiles,
                ConsistencyChecker.class,
                "",
                //Mandated by the checker framework
                "-Anomsgtext",
                //Disable warnings, so that the tests do not fail when there is the warning about using the unannotated jdk
                "-nowarn",
                "-AsuppressWarnings=inconsistent.constructor.type,cast.unsafe",
                "-Astubs=./tests/per-directory/thesis-case-studies/Cassandra.astub;./tests/per-directory/thesis-case-studies/List.astub");
    }

    @Parameterized.Parameters
    public static String[] getTestDirs() {
        return new String[] {
                "per-directory/thesis-case-studies",
        };
    }
}
