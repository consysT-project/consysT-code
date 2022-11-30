package de.tuda.stg.consys.checker.testfiles.legacy;

import de.tuda.stg.consys.annotations.*;
import de.tuda.stg.consys.checker.qual.*;

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
		void set(@Mutable @Strong A a) {}
	}

	class B<T> {
    	void set(int x) { }
	}

    /*
    Tests
     */
	@Transactional
	void testWeakConditionAssignment() {
    	@Strong int s = 0;
    	@Weak int w = 0;

    	if (produceWeak() == 2) {
			// :: error: (assignment.type.implicitflow)
    		s = produceStrong();
    		w = produceWeak();
		}
	}

	@Transactional
	void testStrongConditionAssignment() {
		@Strong int s = 0;
		@Weak int w = 0;

		if (produceStrong() == 2) {
			s = produceStrong();
			w = produceWeak();
		}
	}

	@Transactional
	void testWeakConditionLocalAssignment() {
		// these are inconsistent
		int a = 0;
		int b = 0;

		if (produceWeak() == 2) {
			a = b;
		}
	}

	@Transactional
	void testStrongConditionLocalAssignment() {
		// these are inconsistent
		int a = 0;
		int b = 0;

		if (produceStrong() == 2) {
			a = b;
		}
	}

	@Transactional
	void testWeakConditionMutableArgument() {
		A a = new A();
		@Mutable @Strong A arg = new A();

		if (produceWeak() == 2) {
			// :: error: (invocation.argument.implicitflow)
			a.set(arg);
			a.set(produceWeak());
		}
	}

	@Transactional
	void testWeakConditionMutableReceiver() {
		@Mutable @Strong A m = new A();
		A i = new A();

		if (produceWeak() == 2) {
			// :: error: (invocation.receiver.implicitflow)
			m.set(produceWeak());
			i.set(produceWeak());
		}
	}

	@Transactional
	void testWeakConditionImmutableArgument() {
		A a = new A();

		if (produceWeak() == 2) {
			a.set(produceStrong());
			a.set(produceWeak());
		}
	}

	@Transactional
	void testStrongConditionArgument() {
		A a = new A();

		if (produceStrong() == 2) {
			a.set(produceStrong());
			a.set(produceWeak());
		}
	}

	@Transactional
	void testWeakConditionReceiver() {
		@Weak A w = new A();
		@Strong A s = new A();

		if (produceWeak() == 2) {
			w.set(42);
			// :: error: (invocation.receiver.implicitflow)
			s.set(41);
		}
	}

	@Transactional
	void testStrongConditionReceiver() {
		@Weak A w = new A();
		@Strong A s = new A();

		if (produceStrong() == 2) {
			w.set(42);
			s.set(41);
		}
	}

	@Transactional
	void testWeakConditionReceiverTypeArgument() {
		B<@Weak String> b1 = new B<>();
		B<@Strong String> b2 = new B<>();

		if (produceWeak() == 2) {
			b1.set(42);
			// :: error: (invocation.receiver.implicitflow)
			b2.set(41);
		}
	}

	@Transactional
	void testStrongConditionReceiverTypeArgument() {
		B<@Weak String> b1 = new B<>();
		B<@Strong String> b2 = new B<>();

		if (produceStrong() == 2) {
			b1.set(42);
			b2.set(41);
		}
	}

	@Transactional
	void testAssignmentToStrongInStrongCondition() {
		@Strong int i;

		if (produceStrong() == 2) {
			i = 3;
		}
	}

	@Transactional
	void testAssignmentToWeakInStrongCondition() {
		@Weak int i;

		if (produceStrong() == 2) {
			i = produceStrong();
		}
	}

	@Transactional
	void testAssignmentToStrongInWeakCondition() {
		@Strong int i;

		if (produceWeak() == 2) {
			// :: error: (assignment.type.implicitflow)
			i = 3;
		}
	}
}