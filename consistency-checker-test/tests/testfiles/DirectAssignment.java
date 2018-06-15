import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.checker.qual.Weak;

class DirectAssignment {

	/*
	Helper functions
	 */
    void consumeStrong(@Strong int i) {

    }

    void consumeWeak(@Weak int i) {

    }

    @Strong int produceStrong() {
        return 42;
    }

    @Weak int produceWeak() {
        return 1;
    }

    /*
    Tests
     */
    void testWeakToStrong() {
        int i = produceWeak();
        // :: error: (argument.type.incompatible)
        consumeStrong(i);
    }

	void testStrongToWeak() {
		int i = produceStrong();
		consumeWeak(i);
	}

}