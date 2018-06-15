class MethodAnnotation {

    @Low int getLow() { return 42; }
    @High int getHigh() { return 42; }
    int getAnything() { return 42; }

    void methodAnnotation() {
        @Low int low = getLow();
        low = getHigh();
        low = getAnything();

        @High int high = getHigh();
        // :: error: (assignment.type.incompatible)
        high = getLow();
        // :: error: (assignment.type.incompatible)
        high = getAnything();
    }

    @Low int lowMethodLowReturn() { @Low int low = 42; return low; }
    @Low int lowMethodHighReturn() { @High int high = 42; return high; }

    // :: error: (return.type.incompatible)
    @High int highMethodLowReturn() { @Low int low = 42; return low; }
    @High int highMethodHighReturn() { @High int high = 42; return high; }

}
