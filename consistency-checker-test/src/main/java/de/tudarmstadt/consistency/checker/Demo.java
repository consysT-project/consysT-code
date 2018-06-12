package de.tudarmstadt.consistency.checker;

/**
 * Created on 23.05.18.
 *
 * @author Mirko Köhler
 */
public class Demo {

//	@SuppressWarnings("consistency")
//	private static @PolyConsistent boolean equals(@PolyConsistent Object o1, @PolyConsistent Object o2) {
//		return Objects.equals(o1, o2);
//	}
//
//	public static void f(@Strong String s1, @Weak String s2) {
//		@Weak String w = "welt";
//
//		if (equals(s1, s2)) {
//			String l = "42";
//			String m = s1;
//			s1 = m;
//
//			s2.equals(s1);
//			s1 = s2;
//			s2 = s1;
//
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

//	public static void f2() {
//
//		class B {
//			String g = "3";
//		}
//
//		class A {
//			@Strong String f = "";
//
//			public A() { }
//
//			void accept(B b) {
//				f = b.g;
//			}
//		}
//
//		@Strong A a = new A();
//
//		@Weak B b = new B();
//
//		a.accept(b);
//	}




//	public static void f3(@Weak int k, @Strong int l) {
//
//		class A {
//			@Strong A() { }
//			@Weak A(boolean b) { }
//
//			@Strong Integer get() {
//				return 42;
//			}
//		}
//
//		@Strong A a = new A();
//		A a2 = new A(true);
//
//		if (a == null) {
//			l = 42;
//		}
//	}
//
//	public static void f4(@Strong int s, @Weak int w) {
//		if (w == 42 || (s = 32) == 32) {
//			w = 4;
//		}
//	}

//	public static void f5(@Weak int f, @Weak int g, @Strong int h) {
//
//		class C {
//			@Strong int h;
//			C(@Strong int h) { this.h = h; }
//		}
//
//		class B {
//			int g;
//			B(int g) { this.g = g; }
//		}
//
//		class A {
//			//Fields
//			@Weak int f;
//			@Strong B b;
//			@Weak C c;
//			int x; //implicitly @Inconsistent
//
//			//Constructor
//			@Strong A(@Weak int f, @Strong B b, @Weak C c, int x) {
//				this.f = f;
//				//how is x.y resolved? Does x need to have the consistency level of y?
//				this.b = b;
//				this.c = c;
//				this.x = x;
//			}
//		}
//
//		B b = new B(g);
//		C c = new C(h);
//		A a = new A(f, b, c, 42);
//
//	}


}
