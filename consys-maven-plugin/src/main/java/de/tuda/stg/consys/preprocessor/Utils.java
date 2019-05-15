package de.tuda.stg.consys.preprocessor;

import org.apache.maven.plugin.MojoExecutionException;
import org.apache.maven.project.MavenProject;

import java.io.File;
import java.io.IOException;
import java.util.Iterator;
import java.util.stream.Stream;

/**
 * Created on 18.04.19.
 *
 * @author Mirko Köhler
 */
class Utils {

	//TODO: Ugly workaround, because the Mojo annotation processor cannot use lambdas?!
	//If it works again, use Iterable<Path> iterable = stream::iterator instead.
	static <T> Iterable<T> asIterable(Stream<T> stream) {
		return new Iterable<T>() {
			@Override
			public Iterator<T> iterator() {
				return stream.iterator();
			}
		};
	}

	public static void execute(MavenProject project, File sourceDir, File targetDir) throws MojoExecutionException {
		assert(sourceDir.isDirectory());
		assert(targetDir.isDirectory());

		//Remove the original source directory
		project.getCompileSourceRoots().remove(sourceDir.toString());
		//Added the directory with generated sources
		project.addCompileSourceRoot(targetDir.toString());

		try {
			Preprocessor.preprocessAllFiles(sourceDir.toPath(), targetDir.toPath());
		} catch (IOException e) {
			throw new MojoExecutionException("IO exception during preprocessing", e);
		}
	}

}
