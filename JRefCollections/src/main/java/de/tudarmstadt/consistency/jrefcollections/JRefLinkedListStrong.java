package de.tudarmstadt.consistency.jrefcollections;

import de.tudarmstadt.consistency.checker.qual.Strong;
import de.tudarmstadt.consistency.replobj.japi.JRef;

import java.io.Serializable;
import java.util.Objects;

public class JRefLinkedListStrong implements Serializable {
    public StrongNode head;

    public StrongNode current;

    public StrongNode tail;

    public JRefLinkedListStrong(){
        current = head; tail = head;
    }

    public <T> JRefLinkedListStrong(JRef<@Strong T> item){
        head = new StrongNode<T>(null, null, item);
        current = head; tail = head;
    }

    public void clear(){
        head = null;tail = head; current = head;
    }

    public <T> boolean add(JRef<@Strong T> item){
        if(tail == null){
            StrongNode newNode = new StrongNode<T>(null, null, item);
            head = newNode;tail = head;current = head;
        }else{
            StrongNode newNode = new StrongNode<T>(tail, null, item);
            tail.next = newNode; tail = newNode;
        }
        return true;
    }

    public <T> void add(int index, JRef<@Strong T> item) throws IndexOutOfBoundsException{
        if(size() == index){
            add(item);
        }else if(findIndexFront(index)){
            if(current == null){
                add(item);
            }else{
                StrongNode newNode = new StrongNode<T>(current.prev, current, item);
                current.prev.next = newNode;
                current.prev = newNode; current = head;
            }
        }else throw new IndexOutOfBoundsException("List index out of bounds");
    }

    public <T> JRef<@Strong T> get(int index) throws Exception{
        if(findIndexFront(index)){
            JRef<@Strong T> ret = current.content;
            current = head;
            return ret;
        }else throw new IndexOutOfBoundsException("List index out of bounds");
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
        if(current.next == null){
            return cnt;
        }else{
            current = current.next;
            return sizeRec(cnt + 1);
        }
    }


    //Tries to set current to the node at index index starting from head
    private boolean findIndexFront(int index){
        int remaining = index; current = head;
        if(current == null)
            return false;
        do {
            if(remaining == 0)
                return true;
            current = current.next; remaining--;
        }while (current != null);
        current = head;
        return false;
    }

    //Tries to set current to the node containing o starting from head
    private <T> boolean findObjectFront(JRef<@Strong T> o){
        current = head;
        if(current == null)
            return false;
        do {
            if(current.content.equals(o))
                return true;
            current = current.next;
        }while (current != null);
        current = head;
        return false;
    }
}

class StrongNode <T>implements Serializable {
    public StrongNode prev;

    public StrongNode next;

    public JRef<@Strong T> content;

    StrongNode(StrongNode prev,StrongNode next, JRef<@Strong T> content){
        this.prev = prev;
        this.next = next;
        this.content = content;
    }
}
