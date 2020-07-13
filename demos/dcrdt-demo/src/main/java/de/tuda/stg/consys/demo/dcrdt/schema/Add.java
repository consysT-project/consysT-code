package de.tuda.stg.consys.demo.dcrdt.schema;

import java.io.Serializable;

public class Add extends Event implements Serializable {
    public String element;

    public Add(String s) {
        this.element = s;
    }
}
