package de.tuda.stg.consys.checker.testfiles.legacy;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;

class LocalUsageTest {

	/*
	Helper functions
	 */
    void consumeStrong(@Strong int i) {   }

    void consumeWeak(@Weak int i) {   }

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
    void testUseWeakValue() {
        int i = produceWeak();
        // :: error: (argument.type.incompatible)
        consumeStrong(i);
        consumeWeak(i);
    }

	void testUseStrongValue() {
		int i = produceStrong();
		consumeStrong(i);
		consumeWeak(i);
	}

	void testSimpleFlow() {
    	int i = produceWeak();
    	int j = produceStrong();
    	int a = i + j;

    	i = j;

    	consumeStrong(i);
    	consumeWeak(i);
	}

	void testOperatorFlow() {
		int i = produceWeak();
		int j = produceStrong();
		int a = i + j;

		i = a;

		// :: error: (argument.type.incompatible)
		consumeStrong(i);
		consumeWeak(i);
	}

	void testWeakObject() {
    	A a = new @Weak A();

    	a.set(produceWeak());
    	a.set(produceStrong());
	}


}