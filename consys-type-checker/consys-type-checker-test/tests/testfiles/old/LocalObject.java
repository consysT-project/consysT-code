package de.tuda.stg.consys.checker.testfiles.testfiles.old;

/**
 * Created on 27.05.19.
 *
 * @author Mirko Köhler
 */
public class LocalObject {

	static class A {
		int f;
		A(int f) { this.f = f; }
	}


	void n(A a) {
		A b = new A(32);

		b.f = a.f;
		a.f = b.f;
	}

}
