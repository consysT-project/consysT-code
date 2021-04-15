package de.tuda.stg.consys.checker.testfiles.legacy;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;

class ObjectTest {


	class A {
		int x;
		B b;

		A() {
			x = 42;
			b = new B();
		}

		A(int x, B b) {
			this.x = x;
			this.b = b;
		}
	}

	class B {
		int y;

		B() {
			y = 9;
		}

		B(int y) {
			this.y = y;
		}
	}

	/*
	Helper functions
	 */
    void consumeStrong(@Strong Object i) {   }

    void consumeWeak(@Weak Object i) {   }

    @Strong Object produceStrong() {
        return 42;
    }

    @Weak Object produceWeak() {
        return 1;
    }



    /*
    Tests
     */
    void testStrongObject() {
    	A a = new @Strong A();

    	consumeStrong(a);
    	consumeWeak(a);
    }

	void testWeakObject() {
		A a = new @Weak A();

		// :: error: (argument.type.incompatible)
		consumeStrong(a);
		consumeWeak(a);
	}

	void testStrongFields() {
		A a = new @Strong A();

		//TODO: Define a semantics for these cases
	//	consumeStrong(a.x);
	//	consumeWeak(a.x);
	}


}