package de.tudarmstadt.consistency.jrefcollections;

import com.sun.deploy.panel.JreDialog;
import de.tudarmstadt.consistency.replobj.japi.JRef;

import java.io.Serializable;

public class JRefDistList implements Serializable {

    public Node head;

    public Node current;

    public Node tail;

    public <T> JRefDistList(){
        current = head; tail = head;
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

    public <T> JRef<T> get(int index) throws Exception{
        if(findIndexFront(index)){
            JRef<T> ret = current.content;
            current = head;
            return ret;
        }else throw new IndexOutOfBoundsException("List index out of bounds");
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
}

class DistNode<T> implements Serializable{
    public JRef<T> prev;

    public JRef<T> next;

    public JRef<T> content;

    DistNode(JRef<T> prev, JRef<T> next, JRef<T> content){
        this.prev = prev;
        this.next = next;
        this.content = content;
    }
}
