package de.tuda.stg.consys.preprocessor;

import java.io.*;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.PathMatcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;

/**
 * Created on 18.04.19.
 *
 * @author Mirko Köhler
 */
public class Preprocessor {
	private static final Pattern invokeRegex = Pattern.compile("(?<inv>(\\w+)\\.ref\\(\\)\\.(\\w+)\\((.*)\\))");
	private	static final Pattern setRegex = Pattern.compile("(?<fldset>(\\w+)\\.ref\\(\\)\\.(\\w+)\\s*=\\s*([^\n;]*))");
	private static final Pattern getRegex = Pattern.compile("(?<fldget>(\\w+)\\.ref\\(\\)\\.(\\w+))");


	public static String preprocess(String s0) {

		s0 = invokeRegex.matcher(s0).replaceAll("$2.invoke(\\\"$3\\\", new Object[] \\{$4\\})");
		s0 = setRegex.matcher(s0).replaceAll("$2.setField(\\\"$3\\\", $4)");
		s0 = getRegex.matcher(s0).replaceAll("$2.getField(\\\"$3\\\")");

		return s0;
	}

	public static void preprocessFile(Path input, Path output) throws IOException {

		System.out.println("" + input + " -> " + output);

		try {
			Files.deleteIfExists(output);
			Files.createDirectories(output.getParent());
			Files.createFile(output);
		} catch (IOException e) {
			e.printStackTrace();
			throw e;
		}

		try (
			BufferedReader reader = Files.newBufferedReader(input);
			BufferedWriter writer = Files.newBufferedWriter(output)
		) {
			for (String line : Utils.asIterable(reader.lines())) {
				writer.append(preprocess(line));
				writer.newLine();
			}
		}
	}


	public static void preprocessAllFiles(Path sourcePath, Path targetPath) throws IOException {
		PathMatcher pmatch = FileSystems.getDefault().getPathMatcher("glob:**.java");

		try (Stream<Path> paths = Files.walk(sourcePath)) {

			for (Path input : Utils.asIterable(paths)) {
				if (Files.isRegularFile(input) && pmatch.matches(input)) {
					Path output = targetPath.resolve(sourcePath.relativize(input));
					Preprocessor.preprocessFile(input, output);
				}
			}

		}
	}
}
