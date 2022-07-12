package de.tuda.stg.consys.checker.testfiles.testfiles.old;

/**
 * Created on 27.05.19.
 *
 * @author Mirko Köhler
 */
public class LocalInt {

	void m(int a) {
		int i = 32;
		int j = 31;

		int z = 0;

		if (a < 0) {
			z = i + j;
		}

		z = j;
	}

}
