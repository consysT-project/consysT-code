package de.tuda.stg.consys.examples.collections;


import de.tuda.stg.consys.checker.qual.Inconsistent;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.core.legacy.ConsistencyLabel;
import de.tuda.stg.consys.japi.legacy.JConsistencyLevels;
import de.tuda.stg.consys.japi.legacy.JRef;
import de.tuda.stg.consys.japi.legacy.JReplicaSystem;
import de.tuda.stg.consys.japi.legacy.impl.JReplicaSystems;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.function.Predicate;

public class JRefDistList implements Serializable {

    public JRef head;

    public JRef current;

    public JRef tail;

    public ConsistencyLabel level;

    //A variable to indicate if searching by jref should be done based on
    // exact reference or on the replica, default is false
    public boolean SearchByExactReplica = false;

    //Represents the Size the list thinks it is, used as an approximation to determine if
    // it should be traversed from front to back or back to front
    private int GuessedSize;

    //TODO: Add unsynced and synced functions, rerun benchmarks

    public <T> JRefDistList(ConsistencyLabel level) {
        current = head; this.level = level;
        tail = head;
    }

    public int size(boolean sync){
        if(sync)
            reSyncHead();
        if(head == null){
            return 0;
        }else{
            current = head;
            return sizeRec(1, sync);
        }
    }

    private int sizeRec(int cnt, boolean sync){
        if(sync)
            current.sync();
        if(current.getField("next") == null){
            GuessedSize = cnt;
            return cnt;
        }else{
            current = (JRef) current.getField("next");
            return sizeRec(cnt + 1, sync);
        }
    }

    public <T> JRef<T> removeIndex(int index, boolean sync){
        current = head;
        if(findIndexFront(index, sync)){
            JRef<T> ret = (JRef) current.getField("content");
            JRef prev = ((JRef) current.getField("prev"));
            JRef next = ((JRef) current.getField("next"));

            current.delete();

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
            GuessedSize--;
            return ret;
        }else{
            return null;
        }
    }

    public <T> JRef<T> removeItem(JRef<T> item, boolean sync) {
        current = head;
        if(findItemFront(item, sync)){
            JRef<T> ret = (JRef) current.getField("content");
            JRef prev = ((JRef) current.getField("prev"));
            JRef next = ((JRef) current.getField("next"));

            current.delete();

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
            GuessedSize--;
            return ret;
        }else{
            return null;
        }
    }

    public <T> boolean appendNode(JRef<T> node){
        if (tail == null) {
            head = node;
            tail = head;
            current = head;
        } else {
            tail.invoke("setNext", node);
            node.invoke("setPrev", tail);
            tail = node;
        }
        GuessedSize++;
        return true;
    }

    public <T> boolean append(JRef<T> item) {
        JReplicaSystem system = JReplicaSystems.getSystem();


        JRef<@Inconsistent DistNode> node = system.replicate(new DistNode(item), level);


        if (tail == null) {
            head = node;
            tail = node;
            current = node;
        } else {
            tail.invoke("setNext",node);
            node.invoke("setPrev", tail);
            tail = node;
        }
        GuessedSize++;
        return true;
    }

    public <T> boolean insert(int index, JRef<T> item, boolean sync){
        JReplicaSystem system = JReplicaSystems.getSystem();


        JRef<@Inconsistent DistNode> node = system.replicate(new DistNode(item), level);

        if(findIndexFront(index, sync)){
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
            return true;
        }
        return false;
    }


    public <T> JRef<T> getItem(JRef<T> item, boolean sync) throws Exception{
        if(!findItemFront(item, sync)){
            return null;
        }else{
            JRef<T> ret = (JRef) current.getField("content");
            current = head;
            return ret;
        }
    }

    private <T> boolean findItemFront(JRef<T> item, boolean sync){
        current = head;
        if(sync)
            reSyncHead();
        return recFindItemFront(item, sync);
    }

    private <T> boolean recFindItemFront(JRef<T> item, boolean sync){
        if(current == null){
            return false;
        }else{
            if(sync)
                current.sync();
            if(refEquals((JRef) current.getField("content"),item)){
                return true;
            }else{
                current =(JRef) current.getField("next");
                return recFindItemFront(item, sync);
            }
        }
    }


    public <T> JRef<T> getIndex(int index, boolean sync) throws Exception {

        if(!findIndexFront(index, sync)){
            return null;
        }else{
            JRef<T> ret = (JRef) current.getField("content");
            current = head;
            return ret;
        }
    }

    public JRef<DistNode> getNodeIndex(int index, boolean sync) throws Exception {
        if(!findIndexFront(index, sync)){
            return null;
        }else{
            JRef<DistNode> ret = current;
            current = head;
            return ret;
        }
    }

    public <T> JRef<DistNode> getNodeItem(JRef<T> item, boolean sync) throws Exception{
        if(!findItemFront(item, sync)){
            return null;
        }else{
            JRef<DistNode> ret = current;
            current = head;
            return ret;
        }
    }

    public JRef<DistNode> getNodeNext(JRef<DistNode> start, int diff, boolean sync) throws Exception{
        if(diff <= 0)
            return start;
        current = start;
        if(sync)
            reSyncHead();
        if(!recFindIndexFront(diff, sync)){
            return null;
        }else{
            JRef<DistNode> ret = current;
            current = head;
            return ret;
        }
    }

    private boolean findIndexFront(int index, boolean sync){
        current = head;
        if(sync)
            reSyncHead();
        return recFindIndexFront(index, sync);
    }

    private boolean recFindIndexFront(int index, boolean sync){
        if(current == null){
            return false;
        }else{
            if(sync)
                current.sync();
            if(index == 0){
                return true;
            }else{
                current =(JRef) current.getField("next");
                return recFindIndexFront(index - 1, sync);
            }
        }
    }

    /*
     * Syncing Function that checks if the head has been changed in a remote system.
     * Syncs the head until the new head is found.
     * Only works if the list knows there exists an element in the list, if not the JRefDistList object needs
     * to be synced.
     */
    private boolean reSyncHead(){
        if(head != null){
            head.sync();
            if(head.getField("prev") != null){
                while(head.getField("prev") != null){
                    head = (JRef) head.getField("prev");
                    head.sync();
                }
                return true;
            }
        }
        return false;
    }


    /*
     * Syncing Function that checks if the tail has been changed in a remote system.
     * Syncs the tail until the new tail is found.
     * Only works if the list knows there exists an element in the list, if not the JRefDistList object needs
     * to be synced.
     */
    private boolean reSyncTail(){
        if(tail != null){
            tail.sync();
            if(tail.getField("next") != null){
                while(tail.getField("next") != null){
                    tail = (JRef) tail.getField("next");
                    tail.sync();
                }
                return true;
            }
        }
        return false;
    }

    /*
     * The comparison method used by the list when searching by element. Depends on the set comparison method.
     */
    private boolean refEquals(JRef ref1, JRef ref2){
        if(SearchByExactReplica){
            return ref1.equals(ref2);
        }else{
            return (ref1.toString().equals(ref2.toString()));
        }
    }

    /*
     * Type safety is not guaranteed if the list contains elements of different types.
     * Use with caution. Please ensure that function is serializable by casting
     * (Predicate<T> & Serializable)
     */
    public <T> JRef<@Weak JRefDistList> getWeakReplicaSublist(Predicate<T> function, int searchLimit,boolean sync){

        JReplicaSystem system = JReplicaSystems.getSystem();



        JRef<@Weak JRefDistList> retList = system.replicate(new JRefDistList(JConsistencyLevels.WEAK), JConsistencyLevels.WEAK);


        if(sync)
            reSyncHead();
        current = head;

        boolean limit = true;
        if(searchLimit < 0) limit = false;
        int checked = 0;

        while(current != null){
            if(limit && checked >= searchLimit)
                break;
            T currContent = (T) current.getField("content");
            if(function.test(currContent)){
                retList.invoke("append", currContent);
            }
            current = (JRef) current.getField("next");

            checked++;
        }
        return retList;
    }

    public <T> JRef<T> iterate(boolean reset, boolean sync) throws Exception {
        if(sync) current.sync();
        JRef<T> ret = null;

        if(current != null) {
            ret = (JRef) current.getField("content");
            current = (JRef) current.getField("next");
        }
        if(reset) current = head;

        return ret;
    }

    /*
     * Type safety is not guaranteed if the list contains elements of different types.
     * Use with caution. Please ensure that function is serializable by casting
     * (Predicate<T> & Serializable)
     */
    public <T> LinkedList getNonReplicatedSublist(Predicate<T> function, boolean sync){
        LinkedList<T> retList = new LinkedList<T>();
        if(sync)
            reSyncHead();
        current = head;
        while(current != null){
            T currContent = (T) current.getField("content");
            if(function.test(currContent)){
                retList.add(currContent);
            }

            current = (JRef) current.getField("next");
        }
        return retList;
    }

    public <T> LinkedList getAsNonReplicatedLinkedList(boolean sync){
        LinkedList<T> retList = new LinkedList<T>();
        if(sync)
            reSyncHead();
        current = head;
        while(current != null){
            retList.add((T) current.getField("content"));
            current = (JRef) current.getField("next");
        }
        return retList;
    }

    /*
     * Searchers the list using a predicate, please ensure that function is serializable by casting
     * (Predicate<T> & Serializable)
     */
    public <T> T search(Predicate<T> function, boolean sync){
        if(sync)
            reSyncHead();
        current = head;
        while(current != null){
            T currContent = (T) current.getField("content");
            if(function.test(currContent)){
                return currContent;
            }

            current = (JRef) current.getField("next");
        }
        return null;
    }

    public boolean clear(){
        head = null; tail = null;
        current = head;
        return true;
    }

    public boolean selfDelete(boolean DeleteContent){
        current = head;
        boolean ret = false;
        while (current != null){
            JRef prev = current;
            current = (JRef) current.getField("next");
            if(DeleteContent){
                ((JRef) prev.getField("content")).delete();
            }
            prev.delete();
            ret = true;
        }
        return ret;
    }

    public ArrayList<JRef> getForDelete(){
        ArrayList<JRef> retList = new ArrayList<>();
        current = head;
        while (current != null){
            JRef prev = current;
            current = (JRef) current.getField("next");
            retList.add(current);
        }
        return retList;
    }
}

