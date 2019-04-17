package de.tudarmstadt.consistency.preprocessor;

import org.apache.maven.plugin.AbstractMojo;
import org.apache.maven.plugin.MojoExecutionException;
import org.apache.maven.plugins.annotations.Mojo;

/**
 * Created on 17.04.19.
 *
 * @author Mirko Köhler
 */
@Mojo(name = "sayhi")
public class GreetingMojo extends AbstractMojo {

	public void execute() throws MojoExecutionException {
		getLog().info( "Hello, world." );
	}
}
