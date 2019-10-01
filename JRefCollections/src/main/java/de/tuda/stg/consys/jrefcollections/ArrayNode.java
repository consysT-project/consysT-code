package de.tuda.stg.consys.jrefcollections;

import de.tuda.stg.consys.objects.japi.JRef;

import java.io.Serializable;

public class ArrayNode implements Serializable {

    public ArrayNode(JRef<ArrayNode> prev, JRef<ArrayNode> next, int size){
        this.cont = new String[size][2];
        this.size = size;

        this.prev = prev;
        this.next = next;
    }
    public int size;
    public String key;
    public String[][] cont;

    public JRef<ArrayNode> prev;
    public JRef<ArrayNode> next;

    public String setAt(int index, String key, String val){
        String ret = cont[index][1];
        cont[index][0] = key;
        cont[index][1] = val;
        return ret;
    }

    public void clear(){
        cont = new String[size][2];
    }
}
