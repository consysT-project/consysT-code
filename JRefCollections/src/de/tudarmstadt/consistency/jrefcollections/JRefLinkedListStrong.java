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

    public <T> void add(JRef<@Strong T> item){
        if(tail == null){
            StrongNode newNode = new StrongNode<T>(null, null, item);
            head = newNode;tail = head;current = head;
        }else{
            StrongNode newNode = new StrongNode<T>(tail, null, item);
            tail.next = newNode; tail = newNode;
        }
    }

    public <T> JRef<@Strong T> get(int index) throws Exception{
        Objects.requireNonNull(current, "No Items in the list");
        if(index > 0){
            if(current.next != null){
                current = current.next;
                return get(index - 1);
            }
            else throw new IndexOutOfBoundsException("List index out of bounds");
        }else{
            JRef<@Strong T> ret = current.content;
            current = head;
            return ret;
        }
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
