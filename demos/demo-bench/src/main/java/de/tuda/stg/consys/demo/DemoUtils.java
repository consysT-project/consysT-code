package de.tuda.stg.consys.demo;

/**
 * Created on 19.11.19.
 *
 * @author Mirko Köhler
 */
public class DemoUtils {

	public static void printProgress(int iteration) {
		System.out.print(iteration % 100 == 0 ? iteration : ".");
	}

	public static void printDone() {
		System.out.println(" DONE");
	}
}
