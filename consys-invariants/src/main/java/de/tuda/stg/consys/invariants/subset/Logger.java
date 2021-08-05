package de.tuda.stg.consys.invariants.subset;

import java.text.SimpleDateFormat;
import java.util.Date;

public class Logger {

	private static final SimpleDateFormat sdf = new SimpleDateFormat("hh:mm:ss");

	private static String generateString(String tag, Object msg) {
		var s = String.valueOf(msg);
		return "[" + sdf.format(new Date()) + "][" + tag + "]: " + s;
	}

	public static void info(Object msg) {
		System.out.println(generateString("INFO", msg));
	}

	public static void warn(Object msg) {
		System.err.println(generateString("WARN", msg));
	}

	public static void err(Object msg) {
		System.err.println(generateString("ERR!", msg));
	}

}
