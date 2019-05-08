package de.tudarmstadt.consistency.jrefcollections;

import de.tudarmstadt.consistency.checker.qual.Weak;
import de.tudarmstadt.consistency.replobj.japi.JRef;

import java.io.Serializable;
import java.util.Objects;

public class JRefLinkedListWeak implements Serializable {
    public WeakNode head;

    public WeakNode current;

    public WeakNode tail;

    public JRefLinkedListWeak(){
        current = head; tail = head;
    }

    public <T> JRefLinkedListWeak(JRef<@Weak T> item){
        head = new WeakNode<T>(null, null, item);
        current = head; tail = head;
    }

    public <T> void add(JRef<@Weak T> item){
        if(tail == null){
            WeakNode newNode = new WeakNode<T>(null, null, item);
            head = newNode;tail = head;current = head;
        }else{
            WeakNode newNode = new WeakNode<T>(tail, null, item);
            tail.next = newNode; tail = newNode;
        }
    }

    public <T> boolean remove(JRef<@Weak T> o){
        if(findObject(o)){
            current = current.prev;
            current.next = current.next.next;
            current.next.prev = current;
            current = head;
            return true;
        }else
            return false;
    }

    public boolean remove(int index){
        if(findIndex(index)){
            current = current.prev;
            current.next = current.next.next;
            current.next.prev = current;
            current = head;
            return true;
        }else
            return false;
    }

    public <T> JRef<@Weak T> get(int index) throws Exception{
        Objects.requireNonNull(current, "No Items in the list");
        if(index > 0){
            if(current.next != null){
                current = current.next;
                return get(index - 1);
            }
            else throw new IndexOutOfBoundsException("List index out of bounds");
        }else{
            JRef<@Weak T> ret = current.content;
            current = head;
            return ret;
        }
    }

    public <T> boolean contains(JRef<@Weak T> o){
        return findObject(o);
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

    //Tries to set current to the node at index index
    private boolean findIndex(int index){
        int remaining = index; current = head;
        do {
            if(remaining == 0)
                return true;
            current = current.next; remaining--;
        }while (current != null);
        current = head;
        return false;
    }

    //Tries to set current to the node containing o
    private <T> boolean findObject(JRef<@Weak T> o){
        current = head;
        do {
            if(current.content.equals(o))
                return true;
            current = current.next;
        }while (current != null);
        current = head;
        return false;
    }
}

class WeakNode <T>implements Serializable {
    public WeakNode prev;

    public WeakNode next;

    public JRef<@Weak T> content;

    WeakNode(WeakNode prev,WeakNode next, JRef<@Weak T> content){
        this.prev = prev;
        this.next = next;
        this.content = content;
    }
}
