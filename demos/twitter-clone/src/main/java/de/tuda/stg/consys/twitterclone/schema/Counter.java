package de.tuda.stg.consys.twitterclone.schema;

import java.io.Serializable;
import java.util.UUID;

public class Counter implements Serializable {

    public int value;

    public void inc() {
        value++;
    }

    public Counter(int value) {
        this.value = value;
    }

}