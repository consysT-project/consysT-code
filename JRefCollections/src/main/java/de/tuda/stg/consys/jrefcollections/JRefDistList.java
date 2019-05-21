package de.tuda.stg.consys.jrefcollections;


import de.tuda.stg.consys.objects.japi.JRef;

import java.io.Serializable;

public class JRefDistList implements Serializable {

    public JRef head;

    public JRef current;

    public JRef tail;

    public <T> JRefDistList() {
        current = head;
        tail = head;
    }

    public int size(){
        if(head == null){
            return 0;
        }else{
            current = head;
            return sizeRec(1);
        }
    }

    private int sizeRec(int cnt){
        if(current.getField("next") == null){
            return cnt;
        }else{
            current = (JRef) current.getField("next");
            return sizeRec(cnt + 1);
        }
    }

    public <T> boolean append(JRef<T> node) {
        if (tail == null) {
            head = node;
            tail = head;
            current = head;
        } else {
            tail.invoke("setNext",node);
            node.invoke("setPrev", tail);
            tail = node;
        }
        return true;
    }

    public <T> void insert(int index, JRef<T> node) throws IndexOutOfBoundsException{
        if(size() == index){
            append(node);
        }else if(findIndexFront(index)){
            if(current == null){
                append(node);
            }else{
                node.invoke("setPrev",current.getField("prev"));
                node.invoke("setNext",current);
                ((JRef) current.getField("prev")).invoke("setNext", node);
                current.invoke("setPrev", node); current = head;
            }
        }else throw new IndexOutOfBoundsException("List index out of bounds");
    }

    public <T> JRef<T> getSeq(int index) throws Exception {
        if (findIndexFront(index)) {
            JRef<T> ret = (JRef) current.getField("content");
            current = head;
            return ret;
        } else throw new IndexOutOfBoundsException("List index out of bounds");
    }

    public <T> JRef<T> get(int index) throws Exception {
        if(head == null){
            throw new IndexOutOfBoundsException("List index out of bounds");
        }else{
            current = head;
            return recGet(index);
        }
    }

    private  <T> JRef<T> recGet(int index) throws Exception {
        //current.sync(); //To enable Syncinc here comment out the requirement in the sync function of AkkaReplicatedObject.scala (l. 78)
        if(index == 0){
            JRef<T> ret = (JRef) current.getField("content");
            current = head;
            return ret;
        }else if(current.getField("next") == null){
            throw new IndexOutOfBoundsException("List index out of bounds");
        }else{
            current = (JRef) current.getField("next");
            return recGet(index - 1);
        }
    }

    //Tries to set current to the node at index index starting from head
    private boolean findIndexFront(int index) {
        int remaining = index;
        current = head;
        if (current == null)
            return false;
        do {
            if (remaining == 0)
                return true;
            current = (JRef) current.getField("next");
            remaining--;
        } while (current != null);
        current = head;
        return false;
    }
}

