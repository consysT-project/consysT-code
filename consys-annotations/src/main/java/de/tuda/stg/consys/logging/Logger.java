package de.tuda.stg.consys.logging;

import com.google.common.base.Strings;

import java.io.*;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicInteger;


public class Logger {

	private final static TaggedWriter nullWriter = null; //new TaggedWriter(PrintStream.nullOutputStream(), new String[0]);
	private final static TaggedWriter debugWriter = new TaggedWriter(System.out, new String[] { "DEBUG" });
	private final static TaggedWriter infoWriter = new TaggedWriter(System.out, new String[] { "INFO" });
	private final static TaggedWriter warnWriter = new TaggedWriter(System.out, new String[] { "WARN" });
	private final static TaggedWriter errWriter = new TaggedWriter(System.err, new String[] { "FAIL" });



	public final static PrintWriter debug = new PrintWriter(debugWriter, true);

	public final static PrintWriter info = new PrintWriter(infoWriter, true);

	public final static PrintWriter warn = new PrintWriter(warnWriter, true);

	public final static PrintWriter err = new PrintWriter(errWriter, true);

	private static AtomicInteger identation = new AtomicInteger(0);


	public static void debug(Object msg) { debug.println(msg); }

	public static void debug(Object tag, Object msg) {
		debugWriter.withTags( new String[] { tag.toString() },
				() -> debug.println(msg)
		);
	}

	public static void info(Object msg) { info.println(msg); }

	public static void info(Object tag, Object msg) {
		infoWriter.withTags( new String[] { tag.toString() },
				() -> info.println(msg)
		);
	}

	public static void warn(Object msg) {
		warn.println(msg);
	}

	public static void warn(Object tag, Object msg) {
		warnWriter.withTags( new String[] { tag.toString() },
				() -> warn.println(msg)
		);
	}

	public static void err(Object msg) {
		err.println(msg);
	}

	public static void err(Object tag, Object msg) {
		errWriter.withTags( new String[] { tag.toString() },
				() -> err.println(msg)
		);
	}

	public static void withIdentation(Runnable f) {
		identation.incrementAndGet();
		f.run();
		identation.decrementAndGet();
	}

	private static class TaggedWriter extends Writer {
		private final Writer stream;
		private String[] tags;

		// Indicates whether the last output to this writer was a new line
		private AtomicBoolean first = new AtomicBoolean(true);

		private static final SimpleDateFormat sdf = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss.SSS");

		private TaggedWriter(Writer stream, String[] tags) {
			this.stream = stream;
			this.tags = tags;
		}

		private TaggedWriter(OutputStream stream, String[] tags) {
			this(new OutputStreamWriter(stream), tags);
		}

		public void withTags(String[] additionalTags, Runnable f) {
			synchronized (lock) {
				String[] oldTags = tags;
				String[] newTags = new String[tags.length + additionalTags.length];
				System.arraycopy(tags, 0, newTags, 0, tags.length);
				System.arraycopy(additionalTags, 0, newTags, tags.length, additionalTags.length);

				tags = newTags;
				f.run();
				tags = oldTags;
			}
		}

		@Override
		public void write(int b) throws IOException {
			synchronized (lock) {
				stream.write(b);
			}
		}

		@Override
		public void write(char[] cbuf, int off, int len) throws IOException {
			synchronized (lock) {
				String msg = String.valueOf(cbuf, off, len);

				String prefix = "[" + sdf.format(new Date()) + "]";

				for (String tag : tags) {
					prefix += "[" + tag + "]";
				}

				prefix += Strings.repeat("  |", identation.get()) + " ";

				String s = String.valueOf(msg);

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
		}

		@Override
		public void flush() throws IOException {
			synchronized (lock) {
				stream.flush();
			}
		}

		@Override
		public void close() throws IOException {
			stream.close();
		}
	}




}
