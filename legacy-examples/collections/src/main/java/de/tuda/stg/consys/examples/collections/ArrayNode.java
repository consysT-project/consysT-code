package de.tuda.stg.consys.examples.collections;

import de.tuda.stg.consys.japi.legacy.JRef;

import java.io.Serializable;

public class ArrayNode implements Serializable {

    public ArrayNode(JRef<ArrayNode> prev, JRef<ArrayNode> next, int size){
        this.cont = new JRef[size];
        this.size = size;

        this.prev = prev;
        this.next = next;
        filled = 0;
    }
    public int filled;
    public int size;
    public JRef[] cont;

    public JRef<ArrayNode> prev;
    public JRef<ArrayNode> next;

    public int checkFilled(){
        int x = 0;
        for (JRef ref:cont) {
            if(ref!= null) x++;
        }
        filled = x;
        return x;
    }

    public JRef setAt(int index, JRef val){
        JRef ret = cont[index];
        cont[index] = val;
        return ret;
    }

    public boolean setIfFree(int index, JRef val){
        if(cont[index] == null){
            cont[index] = val;
            return true;
        }
        return false;
    }

    public int makeSpaceAndSet(int index, JRef val){
        checkFilled();
        if(filled == size)
            return -1;
        else{
            int i = 0;
            for(; i < size; i++){
                if(cont[i] == null)
                    break;
            }
            if(i == index){
                cont[index] = val;
                return index;
            }else if(i < index){
                //Shift elements to the left
                for(; i < index-1; i++){
                    cont[i] = cont[i + 1];
                }
                cont[index-1] = val;
                return index-1;
            }else{
                //Shift elements to the right
                for(; i > index; i--){
                    cont[i] = cont[i - 1];
                }
                cont[index] = val;
                return index;
            }
        }
    }

    public boolean append(JRef val){
        if(checkFilled() == size)
            return false;
        if(filled == 0){
            cont[0] = val;
            return true;
        }
        for (int x = size - 1;x > 0;x--){
            if(cont[x] == null && cont[x-1] != null){
                cont[x] = val;
                return true;
            }
        }
        return false;
    }

    public int find(JRef val){
        String valAddr = val.addr();
        for (int x = 0;x < size;x++){
            if(valAddr.equals(cont[x].addr()))
                return x;
        }
        return -1;
    }

    public void clear(){
        cont = new JRef[size];
    }

    /**
     * Deletes all replicas contained in the array node
     * @return true if something was deleted
     */
    public boolean deleteAllContent(){
        boolean ret = false;
        for (JRef ref:cont) {
            if(ref != null){
                ref.delete();
                ret = true;
            }
        }
        return ret;
    }
}
