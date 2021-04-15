package de.tuda.stg.consys.checker.testfiles.legacy;

import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;

class ImplicitFlowTest {

	/*
	Helper functions
	 */
    @Strong int produceStrong() {
        return 42;
    }

    @Weak int produceWeak() {
        return 1;
    }

    class A {
    	void set(int x) { }
	}

	class B<T> {
    	void set(int x) { }
	}

    /*
    Tests
     */
	void testWeakConditionAssignment() {
    	int i = 0;
    	int j = 0;

    	if (produceWeak() == 2) {
			// :: error: (assignment.type.implicitflow)
    		i = produceStrong();
    		j = produceWeak();
		}
	}

	void testStrongConditionAssignment() {
		int i = 0;
		int j = 0;

		if (produceStrong() == 2) {
			i = produceStrong();
			j = produceWeak();
		}
	}

	void testWeakConditionLocalAssignment() {
		int a = 0;
		int b = 0;

		if (produceWeak() == 2) {
			a = b;
		}
	}

	void testStrongConditionLocalAssignment() {
		int a = 0;
		int b = 0;

		if (produceStrong() == 2) {
			a = b;
		}
	}

	void testWeakConditionArgument() {
		A a = new A();

		if (produceWeak() == 2) {
			// :: error: (invocation.argument.implicitflow)
			a.set(produceStrong());
			a.set(produceWeak());
		}
	}

	void testStrongConditionArgument() {
		A a = new A();

		if (produceStrong() == 2) {
			a.set(produceStrong());
			a.set(produceWeak());
		}
	}

	void testWeakConditionReceiver() {
		A a1 = new @Weak A();
		A a2 = new @Strong A();

		if (produceWeak() == 2) {
			a1.set(42);
			// :: error: (invocation.receiver.implicitflow)
			a2.set(41);
		}
	}

	void testStrongConditionReceiver() {
		A a1 = new @Weak A();
		A a2 = new @Strong A();

		if (produceStrong() == 2) {
			a1.set(42);
			a2.set(41);
		}
	}

	void testWeakConditionReceiverTypeArgument() {
		B<@Weak String> b1 = new B<>();
		B<@Strong String> b2 = new B<>();

		if (produceWeak() == 2) {
			b1.set(42);
			// :: error: (invocation.receiver.implicitflow)
			b2.set(41);
		}
	}

	void testStrongConditionReceiverTypeArgument() {
		B<@Weak String> b1 = new B<>();
		B<@Strong String> b2 = new B<>();

		if (produceStrong() == 2) {
			b1.set(42);
			b2.set(41);
		}
	}

	void testAssignmentInStrongCondition1() {
		@Strong int i;

		if (produceStrong() == 2) {
			i = 3;
		}
	}

	void testAssignmentInStrongCondition2() {
		@Weak int i;

		if (produceStrong() == 2) {
			i = produceStrong();
		}
	}

	void testAssignmentInWeakCondition1() {
		@Strong int i;

		if (produceWeak() == 2) {
			// :: error: (assignment.type.implicitflow)
			i = 3;
		}
	}

	void testAssignmentInWeakCondition2() {
		@Weak int i;

		if (produceWeak() == 2) {
			// :: error: (assignment.type.implicitflow)
			i = produceStrong();
		}
	}

}