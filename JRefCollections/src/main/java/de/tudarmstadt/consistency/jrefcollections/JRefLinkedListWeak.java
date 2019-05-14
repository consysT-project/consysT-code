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

    public void clear(){
        head = null;tail = head; current = head;
    }

    public <T> boolean add(JRef<@Weak T> item){
        if(tail == null){
            WeakNode newNode = new WeakNode<T>(null, null, item);
            head = newNode;tail = head;current = head;
        }else{
            WeakNode newNode = new WeakNode<T>(tail, null, item);
            tail.next = newNode; tail = newNode;
        }
        return true;
    }

    public <T> void add(int index, JRef<@Weak T> item) throws IndexOutOfBoundsException{
        if(size() == index){
            add(item);
        }else if(findIndexFront(index)){
            if(current == null){
                add(item);
            }else{
                WeakNode newNode = new WeakNode<T>(current.prev, current, item);
                current.prev.next = newNode;
                current.prev = newNode; current = head;
            }
        }else throw new IndexOutOfBoundsException("List index out of bounds");
    }

    public <T> boolean remove(JRef<@Weak T> o){
        if(findObjectFront(o)){
            current = current.prev;
            current.next = current.next.next;
            current.next.prev = current;
            current = head;
            return true;
        }else
            return false;
    }

    public <T> JRef<@Weak T> remove(int index) throws IndexOutOfBoundsException{
        if(findIndexFront(index)){
            JRef<@Weak T> ret = current.content;
            current = current.prev;
            current.next = current.next.next;
            current.next.prev = current;
            current = head;
            return ret;
        }else throw new IndexOutOfBoundsException("List index out of bounds");
    }

    public <T> JRef<@Weak T> get(int index) throws Exception{
        if(findIndexFront(index)){
            JRef<@Weak T> ret = current.content;
            current = head;
            return ret;
        }else throw new IndexOutOfBoundsException("List index out of bounds");
    }

    public <T> boolean contains(JRef<@Weak T> o){
        return findObjectFront(o);
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
    private <T> boolean findObjectFront(JRef<@Weak T> o){
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
