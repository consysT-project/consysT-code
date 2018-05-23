package de.tu_darmstadt.consistency_types.checker;

import de.tu_darmstadt.consistency_types.checker.qual.PolyConsistent;
import de.tu_darmstadt.consistency_types.checker.qual.Strong;
import de.tu_darmstadt.consistency_types.checker.qual.Weak;

import java.util.Objects;

/**
 * Created on 23.05.18.
 *
 * @author Mirko Köhler
 */
public class Demo {

	static class A {
		@Strong String f = "";

		public A() {

		}

		void accept(B b) {
			f = b.g;
		}
	}

	static class B {
		String g = "3";

	}

//	public static void f(@Strong String s1, @Weak String s2) {
//		@Weak String w = "welt";
//
//		A a = new A();
//
//		if (equals(s1, s2)) {
//			String l = "42";
//			String m = s1;
//			s1 = m;
//
//			s1.equals(s2);
//			s1 = s2;
//			s2 = s1;
//
//			a.f = w;
//
//			@Strong String s = s1;
//			@Strong String s324 = w;
//
//			s1 = "hello";
//			w = "432";
//			System.out.println("this.");
//		}
//
//		int i = 0;
//		if (true) {
//			s1 = "4";
//		}
//
//		s1 = "2";
//	}

	public static void f2() {

		@SuppressWarnings("consistency")
		@Strong A a = new A();

		@Weak B b = new B();

		a.accept(b);
	}

	@SuppressWarnings("consistency")
	public static @PolyConsistent boolean equals(@PolyConsistent Object o1, @PolyConsistent Object o2) {
		return Objects.equals(o1, o2);
	}
}
