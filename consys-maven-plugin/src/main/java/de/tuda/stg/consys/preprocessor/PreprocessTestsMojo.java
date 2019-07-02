package de.tuda.stg.consys.preprocessor;

import org.apache.maven.plugin.AbstractMojo;
import org.apache.maven.plugin.MojoExecutionException;
import org.apache.maven.plugins.annotations.LifecyclePhase;
import org.apache.maven.plugins.annotations.Mojo;
import org.apache.maven.plugins.annotations.Parameter;
import org.apache.maven.project.MavenProject;

import java.io.File;

/**
 * Created on 17.04.19.
 *
 * @author Mirko Köhler
 */
@Mojo(name = "preprocess-tests", defaultPhase = LifecyclePhase.PROCESS_TEST_SOURCES)
public class PreprocessTestsMojo extends AbstractMojo {

	@Parameter(defaultValue = "${project}")
	private MavenProject project;

	@Parameter(property = "preprocess-tests.sourceDir", defaultValue = "${project.build.testSourceDirectory}")
	private File sourceDir;

	@Parameter(property = "preprocess-tests.targetDir", defaultValue = "${project.build.directory}/gen/test/java")
	private File targetDir;


	public void execute() throws MojoExecutionException {
		Utils.execute(project, sourceDir, targetDir);
	}



}
