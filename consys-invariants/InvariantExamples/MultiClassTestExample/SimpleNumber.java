public class SimpleNumber{


    private int value;

    public SimpleNumber(int input) {
        value = input;
    }

    void setValue(int n) {
        value = n;
    }

    int getValue() {
        return value;
    }

    void modify(int change) {
        value += change;
    }

    boolean equals(int n) {
        return (n == value);
    }

}