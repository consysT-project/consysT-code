package de.tuda.stg.consys.examples.collections;

import de.tuda.stg.consys.japi.legacy.JRef;

import java.io.Serializable;

public class KeyJRefPair implements Serializable {
    public KeyJRefPair(String key, JRef ref, boolean valid) {
        this.key = key;
        this.ref = ref;
        this.valid = valid;
    }

    public String key;
    public JRef ref;
    public boolean valid;
}