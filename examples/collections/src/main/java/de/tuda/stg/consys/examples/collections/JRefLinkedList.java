package de.tuda.stg.consys.examples.collections;


import de.tuda.stg.consys.japi.legacy.JRef;

import java.io.Serializable;

public class JRefLinkedList implements Serializable{
    public Node head;

    public Node current;

    public Node tail;

    public JRefLinkedList(){
        current = head; tail = head;
    }

    public <T> JRefLinkedList(JRef<T> item){
        head = new Node<T>(null, null, item);
        current = head; tail = head;
    }

    public void clear(){
        head = null;tail = head; current = head;
    }

    public <T> boolean append(JRef<T> item){
        if(tail == null){
            Node newNode = new Node<T>(null, null, item);
            head = newNode;tail = head;current = head;
        }else{
            Node newNode = new Node<T>(tail, null, item);
            tail.next = newNode; tail = newNode;
        }
        return true;
    }

    public <T> void insert(int index, JRef<T> item) throws IndexOutOfBoundsException{
        if(size() == index){
            append(item);
        }else if(findIndexFront(index)){
            if(current == null){
                append(item);
            }else{
                Node newNode = new Node<T>(current.prev, current, item);
                current.prev.next = newNode;
                current.prev = newNode; current = head;
            }
        }else throw new IndexOutOfBoundsException("List index out of bounds");
    }

    public <T> JRef<T> get(int index) throws Exception{
        if(findIndexFront(index)){
            JRef<T> ret = current.content;
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

    public <T> boolean contains(JRef<T> item){
        return findObjectFront(item);
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
    private <T> boolean findObjectFront(JRef<T> o){
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

class Node<T> implements Serializable {
    public Node<T> next;

    public Node<T> prev;

    public JRef<T> content;

    Node(Node<T> prev, Node<T> next, JRef<T> content){
        this.prev = prev;
        this.next = next;
        this.content = content;
    }
}