package com.github.allprojects.consistencyTypes;

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
                "res/testfiles",
                "-Anomsgtext");
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
