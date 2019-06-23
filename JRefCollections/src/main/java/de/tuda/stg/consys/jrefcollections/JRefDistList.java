package de.tuda.stg.consys.jrefcollections;


import de.tuda.stg.consys.checker.qual.Inconsistent;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.objects.ConsistencyLevel;
import de.tuda.stg.consys.objects.ReplicaSystem;
import de.tuda.stg.consys.objects.japi.JConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;

import java.io.Serializable;

public class JRefDistList implements Serializable {

    public JRef head;

    public JRef current;

    public JRef tail;

    public ConsistencyLevel level;

    //TODO: Add unsynced and synced functions, rerun benchmarks

    public <T> JRefDistList(ConsistencyLevel level) {
        current = head; this.level = level;
        tail = head;
    }

    public int size(){
        if(head == null){
            System.out.println("List is Empty");
            return 0;
        }else{
            current = head;
            return sizeRec(1);
        }
    }

    private int sizeRec(int cnt){
        System.out.println("Element: " + current.toString());
        if(current.getField("next") == null){
            return cnt;
        }else{
            current = (JRef) current.getField("next");
            return sizeRec(cnt + 1);
        }
    }

    public <T> JRef<T> removeIndex(int index){
        current = head;
        if(findIndexFront(index)){
            JRef<T> ret = (JRef) current.getField("content");
            JRef prev = ((JRef) current.getField("prev"));
            JRef next = ((JRef) current.getField("next"));

            if(prev == null && next == null){
                head = null; tail = null;
            }else if(prev == null){
                head = next;
            }else if(next == null){
                tail = prev;
            }else{
                prev.setField("next", next);
                next.setField("prev", prev);
            }
            return ret;
        }else{
            return null;
        }
    }

    public <T> JRef<T> removeItem(JRef<T> item) {
        current = head;
        if(findItemFront(item)){
            JRef<T> ret = (JRef) current.getField("content");
            JRef prev = ((JRef) current.getField("prev"));
            JRef next = ((JRef) current.getField("next"));

            if(prev == null && next == null){
                head = null; tail = null;
            }else if(prev == null){
                head = next;
            }else if(next == null){
                tail = prev;
            }else{
                prev.setField("next", next);
                next.setField("prev", prev);
            }
            return ret;
        }else{
            return null;
        }
    }


    public <T> boolean append(JRef<T> item, JReplicaSystem sys) {
        JRef<@Inconsistent DistNode> node = sys.replicate(new DistNode(item), level);

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

    public <T> void insert(int index, JRef<T> item, JReplicaSystem sys) throws IndexOutOfBoundsException{
        JRef<@Inconsistent DistNode> node = sys.replicate(new DistNode(item), level);

        if(size() == index){
            append(item, sys);
        }else if(findIndexFront(index)){
            if(current.getField("prev") == null){
                head = node; node.invoke("setNext",current);
                current.invoke("setPrev",node);
            }else{
                node.invoke("setPrev",current.getField("prev"));
                node.invoke("setNext",current);

                JRef prevprev = ((JRef) current.getField("prev"));
                prevprev.invoke("setNext", node);
                current.invoke("setPrev", node);
            }
            current = head;
        }else throw new IndexOutOfBoundsException("List index out of bounds");
    }


    public <T> JRef<T> getItem(JRef<T> item) throws Exception{
        if(!findItemFront(item)){
            return null;
        }else{
            JRef<T> ret = (JRef) current.getField("content");
            current = head;
            return ret;
        }
    }

    private <T> boolean findItemFront(JRef<T> item){
        current = head;
        return recFindItemFront(item);
    }

    private <T> boolean recFindItemFront(JRef<T> item){
        if(current == null){
            return false;
        }else{
            current.sync();
            if(current.getField("content").equals(item)){
                return true;
            }else{
                current =(JRef) current.getField("next");
                return recFindItemFront(item);
            }
        }
    }


    public <T> JRef<T> getIndex(int index) throws Exception {

        if(!findIndexFront(index)){
            return null;
        }else{
            JRef<T> ret = (JRef) current.getField("content");
            current = head;
            return ret;
        }
    }

    private boolean findIndexFront(int index){
        current = head;
        return recFindIndexFront(index);
    }

    private boolean recFindIndexFront(int index){
        if(current == null){
            return false;
        }else{
            current.sync();
            if(index == 0){
                return true;
            }else{
                current =(JRef) current.getField("next");
                return recFindIndexFront(index - 1);
            }
        }
    }
}

class DistNode<T> implements Serializable {
    public JRef<T> prev;

    public JRef<T> next;

    public JRef<T> content;

    public DistNode(JRef<T> content) {
        this.content = content;
    }

    public void setPrev(JRef prev) {
        this.prev = prev;
    }

    public void setNext(JRef next) {
        this.next = next;
    }
}

