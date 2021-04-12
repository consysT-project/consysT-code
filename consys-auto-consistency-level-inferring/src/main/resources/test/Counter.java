class Counter {
    //@ public invariant value >= 0;
    int value = 0;

    //@ ensures value == 0;
    public Counter() {}

    /*@
    @ ensures \old(value) + 1 == value;
    @*/
    void inc() {
        value = value + 1;
    }

    /*@
    @ requires value >= 1;
    @ requires true;
    @ ensures value == \old(value) - 1;
    @ ensures true;
    @*/
    void dec() {
        if (value >= 1) value = value - 1;
    }

    /*@
    @ ensures \result == value;
    @ assignable \nothing;
    @*/
    public int getValue() {
        return value;
    }

    /*@
    @ requires true;
    @ ensures (value == \old(value)) || (value == other.value);
    @*/
    void merge(Counter other) {
        //This resembles the LWW merge
        int newVal = other.value;
        value = newVal;
    }
}