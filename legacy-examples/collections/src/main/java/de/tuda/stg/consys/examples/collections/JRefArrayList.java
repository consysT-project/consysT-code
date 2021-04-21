package de.tuda.stg.consys.examples.collections;

import de.tuda.stg.consys.checker.qual.Inconsistent;
import de.tuda.stg.consys.checker.qual.Strong;
import de.tuda.stg.consys.checker.qual.Weak;
import de.tuda.stg.consys.core.legacy.ConsistencyLabel;
import de.tuda.stg.consys.core.legacy.akka.AkkaReplicaSystem;
import de.tuda.stg.consys.japi.legacy.JConsistencyLevels;
import de.tuda.stg.consys.japi.legacy.JRef;
import de.tuda.stg.consys.japi.legacy.JReplicaSystem;
import de.tuda.stg.consys.japi.legacy.JReplicated;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.Optional;
import java.util.function.Predicate;

public class JRefArrayList implements Serializable, JReplicated {

    /* This field is needed for JReplicated */
    public transient AkkaReplicaSystem replicaSystem = null;

    public JRef<ArrayNode> head;

    public JRef<ArrayNode> current;

    public JRef<ArrayNode> tail;

    public int arraySize;

    public ConsistencyLabel level;


    public <T> JRefArrayList(ConsistencyLabel level, int arraySize) {
        current = head; this.level = level;
        tail = head; this.arraySize=arraySize;
    }

    public int size(boolean sync){
        if(sync)
            reSyncHead();
        if(head == null){
            return 0;
        }else{
            current = head;
            return sizeRec(0, sync);
        }
    }

    private int sizeRec(int cnt, boolean sync){
        if(sync){
            current.sync();
        }
        if(current.ref().next == null){
            int x = (int) current.ref().checkFilled();
            return cnt + x;
        }else{
            int x = (int) current.ref().checkFilled();
            current = (JRef) current.ref().next;
            return sizeRec(cnt + x, sync);
        }
    }

    public <T> JRef<T> removeIndex(int index, boolean sync){
        current = head;
        if(findIndexFront(index, sync) >= 0){
            JRef ret = (JRef) current.ref().setAt(index, null);
            return ret;
        }else{
            return null;
        }
    }

    public <T> JRef<T> removeItem(JRef<T> item, boolean sync) {
        current = head;
        int found = findItemFront(item, sync);
        if(found >= 0){

            JRef ret = (JRef) current.invoke("setAt", found, null);
            int filled = (int) current.invoke("checkFilled");

            if(filled <= 0){
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
            }
            return ret;
        }else{
            return null;
        }
    }

    public <T> boolean append(JRef<T> item) {
        Optional<JReplicaSystem> systemOptional = getSystem();
        JReplicaSystem system;
        if(systemOptional.isPresent())
            system = systemOptional.get();
        else
            return false;

        if(tail != null)
            tail.sync();

        if (tail == null) {
            JRef<@Inconsistent ArrayNode> node = system.replicate(new ArrayNode(null,null,arraySize), level);
            head = node;
            tail = head;
            current = head;
        }
        if((boolean)tail.invoke("append", item)){
            return true;
        }
        else{
            JRef<@Inconsistent ArrayNode> node = system.replicate(new ArrayNode(tail,null,arraySize), level);
            tail.setField("next",node);
            tail = node;
        }
        return true;
    }

    public <T> boolean insert(int index, JRef<T> item, boolean sync){
        Optional<JReplicaSystem> systemOptional = getSystem();
        JReplicaSystem system;
        if(systemOptional.isPresent())
            system = systemOptional.get();
        else
            return false;

        int found = findIndexFront(index, sync);
        if(found>=0){
            if((int) current.invoke("checkFilled") < arraySize){
                //There is a free spot, shift existing elements to make space
                if((int)current.invoke("makeSpaceAndSet", found, item)>0)
                    return true;
                else{
                    System.out.println("Something went wrong in the insert function of JRefArrayList, " +
                            "array should have been empty, but it was not.");
                    return false;
                }
            }else{
                //There is no free spot, make a new node and move the elements
                // in front of found to the new node and insert the item after them
                JRef prev = (JRef) current.getField("prev");
                JRef<@Inconsistent ArrayNode> node = system.replicate(new ArrayNode(prev,current,arraySize), level);
                if(prev == null)
                    head = node;
                else
                    prev.setField("next", node);
                current.setField("prev", node);

                JRef[] currCont = (JRef[]) current.getField("cont");
                JRef[] newNodeCont = new JRef[arraySize];
                for(int x = 0;x<found;x++){
                    newNodeCont[x] = currCont[x];
                    currCont[x] = null;
                }
                newNodeCont[found] = item;
                current.ref().cont = currCont;
                current.invoke("checkFilled");
                node.setField("cont", newNodeCont);
                node.invoke("checkFilled");
                current = head;
                return true;
            }
        }
        return false;
    }


    public <T> JRef<T> getItem(JRef<T> item, boolean sync) throws Exception{
        int found = findItemFront(item, sync);
        if(found < 0){
            return null;
        }else{
            JRef[] arr = (JRef[]) current.getField("cont");
            current = head;
            return arr[found];
        }
    }

    private <T> int findItemFront(JRef<T> item, boolean sync){
        current = head;
        if(sync)
            reSyncHead();
        return recFindItemFront(item, sync);
    }

    private <T> int recFindItemFront(JRef<T> item, boolean sync){
        if(current == null){
            return -1;
        }else{
            if(sync)
                current.sync();
            int found = (int) current.invoke("find");
            if(found >= 0){
                return found;
            }else{
                current =(JRef) current.getField("next");
                return recFindItemFront(item, sync);
            }
        }
    }


    public <T> JRef<T> getIndex(int index, boolean sync) {
        int found = findIndexFront(index, sync);
        if(found < 0){
            return null;
        }else{
            JRef[] arr = (JRef[]) current.getField("cont");
            current = head;
            return arr[found];
        }
    }

    private int findIndexFront(int index, boolean sync){
        current = head;
        if(sync)
            reSyncHead();
        return recFindIndexFront(index, sync);
    }

    private int recFindIndexFront(int index, boolean sync){
        if(current == null){
            return -1;
        }else{
            if(sync)
                current.sync();
            int x = (int) current.invoke("checkFilled");
            if(index < x){
                //The element to find is in this node
                return index;
            }else{
                current =(JRef) current.getField("next");
                return recFindIndexFront(index - x, sync);
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
     * Type safety is not guaranteed if the list contains elements of different types.
     * Use with caution. Please ensure that function is serializable by casting
     * (Predicate<T> & Serializable)
     */
    public <T> JRef<@Weak JRefArrayList> getWeakReplicaSublist(Predicate<T> function, int searchLimit, boolean sync){
        Optional<JReplicaSystem> systemOptional = getSystem();
        JReplicaSystem system;
        if(systemOptional.isPresent())
            system = systemOptional.get();
        else
            return null;

        JRef<@Weak JRefArrayList> retList = system.replicate(new JRefArrayList(JConsistencyLevels.WEAK, arraySize),
                JConsistencyLevels.WEAK);

        if(sync)
            reSyncHead();
        current = head;
        int found = 0;
        boolean cont = true;
        while(current != null && cont){
            current.sync();
            T[] currContent = (T[]) current.getField("cont");
            for (T contElement:currContent) {
                if(contElement!= null){
                    if(found >= searchLimit){
                        cont=false;
                        break;
                    }
                    if(function.test(contElement)){
                        retList.invoke("append", contElement);
                        found++;
                    }
                }
            }
            current = (JRef) current.getField("next");
        }
        current = head;
        return retList;
    }


    public <T> JRef<@Strong JRefArrayList> getStrongReplicaSublist(Predicate<T> function, int searchLimit, boolean sync){
        Optional<JReplicaSystem> systemOptional = getSystem();
        JReplicaSystem system;
        if(systemOptional.isPresent())
            system = systemOptional.get();
        else
            return null;

        JRef<@Strong JRefArrayList> retList = system.replicate(new JRefArrayList(JConsistencyLevels.STRONG, arraySize),
                JConsistencyLevels.STRONG);

        if(sync)
            reSyncHead();
        current = head;

        int found = 0;
        boolean cont = true;
        while(current != null && cont){
            if(sync)
                current.sync();

            T[] currContent = (T[]) current.getField("cont");
            for (T contElement:currContent) {
                if(contElement!= null){
                    if(found >= searchLimit){
                        cont=false;
                        break;
                    }
                    if(function.test(contElement)){
                        retList.invoke("append", contElement);
                        found++;
                    }
                }
            }
            current = (JRef) current.getField("next");
        }
        current = head;
        return retList;
    }

    public <T> JRef<T> iterate(boolean reset, boolean sync) throws Exception {
        if(sync) current.sync();
        JRef<T> ret = null;

        if(current != null) {
            ret = (JRef) current.getField("cont");
            current = (JRef) current.ref().next;
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
            if(sync)
                current.sync();

            JRef[] currContent = current.ref().cont;
            if(function.test((T) currContent)){
                retList.add((T) currContent);
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
            if(sync)
                current.sync();

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
            if(sync)
                current.sync();

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

    public JRef CreateCondensedWeakCopy() throws Exception {
        Optional<JReplicaSystem> systemOptional = getSystem();
        JReplicaSystem system;
        if(systemOptional.isPresent())
            system = systemOptional.get();
        else
            return null;

        JRef ret = system.replicate(new JRefArrayList(JConsistencyLevels.WEAK,arraySize), JConsistencyLevels.WEAK);
        int cnt = size(true);
        for(int i=0;i<cnt;i++){
            ret.invoke("append", getIndex(i, true));
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
