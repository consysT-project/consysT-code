package de.tuda.stg.consys.maven.plugins.shade.resource;

import org.apache.maven.plugins.shade.relocation.Relocator;
import org.apache.maven.plugins.shade.resource.ResourceTransformer;
import org.codehaus.plexus.util.IOUtil;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.LinkedList;
import java.util.List;
import java.util.jar.JarEntry;
import java.util.jar.JarOutputStream;

/**
 * Created on 18.11.19.
 *
 * @author Mirko Köhler
 */
public class ReverseAppendingTransformer implements ResourceTransformer {

	String resource;

	List<ByteArrayOutputStream> inputBuffer = new LinkedList<>();

	@Override
	public boolean canTransformResource(String s) {
		return resource != null && resource.equalsIgnoreCase(s);
	}

	@Override
	public void processResource(String s, InputStream inputStream, List<Relocator> list) throws IOException {
		ByteArrayOutputStream newBuffer = new ByteArrayOutputStream();

		IOUtil.copy(inputStream, newBuffer);
		newBuffer.write('\n');

		inputBuffer.add(0, newBuffer);
	}

	@Override
	public boolean hasTransformedResource() {
		return inputBuffer.size() > 0;
	}

	@Override
	public void modifyOutputStream(JarOutputStream jarOutputStream) throws IOException {
		jarOutputStream.putNextEntry(new JarEntry(resource));
		for (ByteArrayOutputStream out : inputBuffer) {
			jarOutputStream.write(out.toByteArray());
			out.close();
		}
		inputBuffer.clear();
	}
}
