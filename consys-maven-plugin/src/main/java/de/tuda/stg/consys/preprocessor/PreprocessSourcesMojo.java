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
@Mojo(name = "preprocess-sources", defaultPhase = LifecyclePhase.PROCESS_SOURCES)
public class PreprocessSourcesMojo extends AbstractMojo {

	@Parameter(defaultValue = "${project}")
	private MavenProject project;

	@Parameter(property = "preprocess-sources.sourceDir", defaultValue = "${project.build.sourceDirectory}")
	private File sourceDir;

	@Parameter(property = "preprocess-sources.targetDir", defaultValue = "${project.build.directory}/generated-sources/main/java")
	private File targetDir;


	public void execute() throws MojoExecutionException {
		Utils.execute(project, sourceDir, targetDir);
	}



}
