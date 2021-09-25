package demos.twitter.consyst;

import java.io.Serializable;

public class Counter implements Serializable {
    private int value;

    public Counter(int value) {
        this.value = value;
    }

    public void inc() {
        value++;
    }

    public int get() {
        return value;
    }
}