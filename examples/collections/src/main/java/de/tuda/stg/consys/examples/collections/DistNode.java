package de.tuda.stg.consys.examples.collections;


import de.tuda.stg.consys.japi.legacy.JRef;

import java.io.Serializable;

class DistNode<T> implements Serializable {
    public JRef<T> prev;

    public JRef<T> next;

    public JRef<T> content;

    public DistNode(JRef<T> content) {
        this.content = content;
    }

    public void setPrev(JRef prev) {
        this.prev = prev;
    }

    public void setNext(JRef next) {
        this.next = next;
    }
}