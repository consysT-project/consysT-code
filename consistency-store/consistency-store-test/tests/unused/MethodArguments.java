class MethodArguments {
    void wantsHigh(@High int a) { }
    void wantsLow(@Low int a) { }
    void wantsAnything(int a) { }

    void methodArguments() {
        @High int high = 42;
        @Low int low = 21;

        wantsHigh(high);
        // :: error: (argument.type.incompatible)
        wantsHigh(low);

        wantsLow(high);
        wantsLow(low);

        wantsAnything(high);
        wantsAnything(low);
    }
}
