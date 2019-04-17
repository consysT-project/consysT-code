package de.tudarmstadt.consistency.concert;

import java.io.Serializable;

class Band implements Serializable {
    public String name;

    public Band(String name) {
        this.name = name;
    }
}
