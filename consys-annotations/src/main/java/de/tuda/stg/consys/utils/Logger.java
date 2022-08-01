package de.tuda.stg.consys.utils;

import com.google.common.base.Strings;

import java.io.*;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;

public class Logger {

	public final static PrintWriter info = newTaggedPrinter(System.out, "INFO");
	public final static PrintWriter warn = newTaggedPrinter(System.err, "WARN");
	public final static PrintWriter err = newTaggedPrinter(System.err, "ERR!");

	private static AtomicInteger identation = new AtomicInteger(0);

	public static void info(Object msg) {
		info.println(msg);
	}

	public static void warn(Object msg) {
		warn.println(msg);
	}

	public static void err(Object msg) {
		err.println(msg);
	}

	public static void withIdentation(Runnable f) {
		identation.incrementAndGet();
		f.run();
		identation.decrementAndGet();
	}

	private static PrintWriter newTaggedPrinter(OutputStream out, String tag) {
		return new PrintWriter(new TaggedWriter(out, tag), true);
	}

	private static class TaggedWriter extends Writer {
		private final Writer stream;
		private final String tag;

		// Indicates whether the last output to this writer was a new line
		private AtomicBoolean first = new AtomicBoolean(true);

		private final SimpleDateFormat sdf = new SimpleDateFormat("HH:mm:ss");

		private TaggedWriter(Writer stream, String tag) {
			this.stream = stream;
			this.tag = tag;
		}

		private TaggedWriter(OutputStream stream, String tag) {
			this(new OutputStreamWriter(stream), tag);
		}

		@Override
		public void write(int b) throws IOException {
			stream.write(b);
		}

		@Override
		public void write(char[] cbuf, int off, int len) throws IOException {
			var msg = String.valueOf(cbuf, off, len);

			var prefix = "[" + sdf.format(new Date()) + "][" + tag + "]" + Strings.repeat("  |", identation.get()) + " ";

			var s = String.valueOf(msg);

			if (first.compareAndSet(true, false)) {
				s = prefix + s;
			}

			if (s.charAt(s.length() - 1) == '\n') {
				first.set(true);
				s = s.substring(0, s.length() - 1).replace("\n", "\n" + prefix) + "\n";
			} else {
				s = s.replace("\n", "\n" + prefix);
			}
			stream.write(s, 0, s.length());
		}

		@Override
		public void flush() throws IOException {
			stream.flush();
		}

		@Override
		public void close() throws IOException {
			stream.close();
		}
	}




}
