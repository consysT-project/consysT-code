package de.tuda.stg.consys.examples.collections;

import de.tuda.stg.consys.japi.legacy.JRef;

import java.io.Serializable;

public class StringNode implements Serializable {

    public StringNode(JRef<StringNode> prev, JRef<StringNode> next){
        filled = false;

        this.prev = prev;
        this.next = next;
    }

    public boolean filled;
    public String key;
    public String cont;

    public JRef<StringNode> prev;
    public JRef<StringNode> next;

}
