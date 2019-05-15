package de.tuda.stg.consys.concert;

import java.io.Serializable;

class Band implements Serializable {
    public String name;

    public Band(String name) {
        this.name = name;
    }
}
