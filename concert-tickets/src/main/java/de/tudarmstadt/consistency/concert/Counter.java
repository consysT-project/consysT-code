package de.tudarmstadt.consistency.concert;

import java.io.Serializable;

public class Counter implements Serializable {
    public int value;
    public void inc() {
        value++;
    }

    public Counter(int value) {
        this.value = value;
    }
}
