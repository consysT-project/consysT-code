package de.tudarmstadt.consistency.checker;

import org.checkerframework.framework.test.CheckerFrameworkPerFileTest;
import org.junit.runners.Parameterized.Parameters;

import java.io.File;

public class ConsistencyTest extends CheckerFrameworkPerFileTest {

    public ConsistencyTest(File file) {
        super(
                file,
                ConsistencyChecker.class,
                "testfiles",
                //Mandated by the checker framework
				"-Anomsgtext",
				//Disable warnings, so that the tests do not fail when there is the warning about using the unannotated jdk
				"-nowarn");
    }

//    @Parameters
//    public static List<File> getTestFiles() {
//
//
//
//        File dir = new File ("/consistencyCheckerTest/consistency");
//        List<File> files = new ArrayList<File>();
//        files.addAll(Arrays.asList(dir.listFiles()));
//        return files;
//    }

	@Parameters
	public static String[] getTestDirs() {
    	return new String[] {"testfiles"};
	}
}
