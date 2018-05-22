package de.tu_darmstadt.consistency_types.utils;

import java.io.PrintStream;
import java.text.SimpleDateFormat;
import java.util.Date;
import java.util.Objects;

/**
 * Created on 22.05.18.
 *
 * @author Mirko Köhler
 */
public class Log {

	private static SimpleDateFormat sdf = new SimpleDateFormat("hh:mm:ss.SS");

	private static String prefix(Class<?> clazz) {
		return String.format("[%s][%s]: ", sdf.format(new Date()), clazz != null ? clazz.getSimpleName() : "UNKNOWN");
	}

	private static String infoToString(Class<?> clazz, Object text) {
		return prefix(clazz) + Objects.toString(text);
	}

	private static PrintStream out = System.out;

	public static void info(Class<?> clazz, Object text) {
		out.println(infoToString(clazz, text));
	}
}
