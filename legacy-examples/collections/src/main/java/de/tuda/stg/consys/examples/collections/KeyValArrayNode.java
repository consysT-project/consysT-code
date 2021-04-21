package de.tuda.stg.consys.examples.collections;

import de.tuda.stg.consys.japi.legacy.JRef;

import java.io.Serializable;

public class KeyValArrayNode implements Serializable {

    public KeyValArrayNode(JRef<KeyValArrayNode> prev, JRef<KeyValArrayNode> next, int size){
        this.cont = new String[size][2];
        this.size = size;

        this.prev = prev;
        this.next = next;
    }
    public int size;
    public String[][] cont;

    public JRef<KeyValArrayNode> prev;
    public JRef<KeyValArrayNode> next;

    public String setAt(int index, String key, String val){
        String ret = cont[index][1];
        cont[index][0] = key;
        cont[index][1] = val;
        System.out.flush();
        return ret;
    }

    public void clear(){
        cont = new String[size][2];
    }
}
