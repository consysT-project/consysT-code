package de.tuda.stg.consys.demo.dcrdt.schema;

import java.io.Serializable;

public class Remove extends Event implements Serializable {

    public String element;

    public Remove(String s){
        this.element = s;
    }
}
