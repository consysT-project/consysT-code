package de.tuda.stg.consys.checker.testfiles.legacy;

import de.tuda.stg.consys.annotations.*;
import de.tuda.stg.consys.checker.qual.*;

class ObjectTest {
	class A {
		int x;
		B b;
	}

	class B {
		int y;
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
	@Transactional
    void testStrongObject() {
		@Strong A a = new A();

    	consumeStrong(a);
    	consumeWeak(a);
    }

	@Transactional
	void testWeakObject() {
		@Weak A a = new A();

		// :: error: (argument)
		consumeStrong(a);
		consumeWeak(a);
	}

	@Transactional
	void testStrongFields() {
		@Strong A a = new A();

		consumeStrong(a.x);
		consumeWeak(a.x);
	}

	@Transactional
	void testWeakFields() {
		@Weak A a = new A();

		// :: error: (argument)
		consumeStrong(a.x);
		consumeWeak(a.x);
	}
}