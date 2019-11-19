package de.tuda.stg.consys.demo.concert.schema;

import java.io.Serializable;

public class Band implements Serializable {
    public String name;

    public Band(String name) {
        this.name = name;
    }
}
