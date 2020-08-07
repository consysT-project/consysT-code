package de.tuda.stg.consys.demo.dcrdt.schema;

import java.io.Serializable;

/**
 * @author = Kris Frühwein, Julius Näumann
 * Event for the Dot-Store that represents the addition of an element
 */

public class Add extends Event implements Serializable {
    public String element;

    /**
     * Constructor
     * @param s The String that should be added
     */
    public Add(String s) {
        this.element = s;
    }
}
