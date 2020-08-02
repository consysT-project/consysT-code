package de.tuda.stg.consys.demo.dcrdt.schema;

import java.io.Serializable;

/**
 * @author = Kris Frühwein, Julius Näumann
 * Event for the Dot-Store that represents the removal of an element
 */
public class Remove extends Event implements Serializable {

    public String element;

    /**
     * Constructor
     * @param s The String that should be removed
     */
    public Remove(String s){
        this.element = s;
    }
}
