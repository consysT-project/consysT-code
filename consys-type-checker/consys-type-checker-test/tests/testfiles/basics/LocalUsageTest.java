package de.tuda.stg.consys.checker.testfiles.legacy;

import de.tuda.stg.consys.annotations.*;
import de.tuda.stg.consys.checker.qual.*;

class LocalUsageTest {

	/*
	Helper functions
	 */
    void consumeStrong(@Strong int i) { }

    void consumeWeak(@Weak int i) { }

    @Strong int produceStrong() {
        return 42;
    }

    @Weak int produceWeak() {
        return 1;
    }

    class A {
    	void set(int x) { };
	}


    /*
    Tests
     */
	@Transactional
    void testUseWeakValue() {
        @Weak int i = produceWeak();
        // :: error: (argument)
        consumeStrong(i);
        consumeWeak(i);
    }

	@Transactional
	void testUseStrongValue() {
		@Strong int i = produceStrong();
		consumeStrong(i);
		consumeWeak(i);
	}

	@Transactional
	void testSimpleFlow() {
    	@Weak int i = produceWeak();
    	@Strong int j = produceStrong();

		@Weak int a = i + j;

    	i = j;

		// :: error: (argument)
    	consumeStrong(i);
    	consumeWeak(i);
	}

	@Transactional
	void testOperatorFlow() {
		@Weak int i = produceWeak();
		@Strong int j = produceStrong();

		@Weak int a = i + j;

		i = a;

		// :: error: (argument)
		consumeStrong(i);
		consumeWeak(i);
	}
}