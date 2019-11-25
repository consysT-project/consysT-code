package de.tuda.stg.consys.demo.concert.schema;

import java.io.Serializable;

public class Counter implements Serializable {
    public Integer value;
    public void inc() {
        value++;
    }

    public Counter(int value) {
        this.value = value;
    }
}
