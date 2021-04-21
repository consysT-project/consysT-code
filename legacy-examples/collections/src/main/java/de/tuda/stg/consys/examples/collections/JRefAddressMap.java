package de.tuda.stg.consys.examples.collections;

import de.tuda.stg.consys.core.legacy.ConsistencyLabel;
import de.tuda.stg.consys.core.legacy.akka.AkkaReplicaSystem;
import de.tuda.stg.consys.japi.legacy.JRef;
import de.tuda.stg.consys.japi.legacy.JReplicaSystem;
import de.tuda.stg.consys.japi.legacy.impl.JReplicaSystems;

import java.io.Serializable;

public class JRefAddressMap implements Serializable {
    /*
    Basically a Hashmap with an identity crisis
     */

    /* This field is needed for JReplicated */
    public transient AkkaReplicaSystem replicaSystem = null;

    final double maxLoadFactor = 0.75;
    final double resizeFactor = 1.4;

    private JRef<StringNode> head;
    private JRef<StringNode> tail;
    private JRef<StringNode> current;

    ConsistencyLabel level;

    private double loadFactor;
    private int filled;
    private int nodeCount;

    public int size() {
        return filled;
    }

    public JRefAddressMap() {
    }

    public boolean init(int initial_size, ConsistencyLabel level) throws Exception{
        JReplicaSystem system = JReplicaSystems.getSystem();


        this.level = level;
        filled = 0;
        head = system.replicate(new StringNode(null, null), level);
        tail = head;
        for(int i = 0;i<initial_size - 1;i++){
            addNode(tail);
        }
        nodeCount = countNodes();
        loadFactor = (filled / nodeCount);
        return true;
    }

    private boolean addNode(JRef<StringNode> previous){
        JReplicaSystem system = JReplicaSystems.getSystem();


        JRef<StringNode> newNode = system.replicate(new StringNode(previous, previous.getField("next")), level);
        if(newNode.getField("next") == null){
            tail = newNode;
        }else{
            ((JRef) newNode.getField("next")).setField("prev", newNode);
        }
        previous.setField("next", newNode);

        return true;
    }

    private int countNodes(){
        current = head;
        int cnt = 0;
        while(current != null){
            current = current.getField("next");
            cnt++;
        }
        return cnt;
    }

    private boolean goTo(int index){
        current = head;
        if(index > nodeCount - 1)
            return false;
        else{
        int curr = 0;
        while(curr < index){
            current = current.getField("next");
            curr++;
        }
        }
        return true;
    }

    /*
    Takes a jref and stores its address in the hashmap
     */
    public <T> String put(String key, JRef<T> value) {
        int index = hash(key) % nodeCount;
        if(goTo(index)){
            int currPos = index;
            String val = value.addr();
            do {
                if (current.getField("filled")) {
                    if (current.getField("key").equals(key)) {
                        //The key is already in the map and is simply replaced
                        current.setField("cont",val);
                        return val;
                    } else
                        //keep searching
                        if((currPos + 1) % nodeCount < currPos){
                            currPos = (currPos + 1) % nodeCount;
                            goTo(currPos);
                        }else{
                            currPos++;
                            current = current.getField("next");
                        }
                } else {
                    //there is an empty slot
                    current.setField("key", key);
                    current.setField("cont", val);
                    current.setField("filled", true);
                    filled++;
                    checkLoad();
                    return null;
                }
            } while (currPos != index);
        }
        return null;
    }

    public boolean containsKey(String key) {
		return getValue(key) != null;
    }

    public boolean containsValue(JRef value){
		return getKey(value) != null;
    }

    public String getKey(JRef value){
        int currPos = 0;
        int checkedPairs = 0;

        if(filled == 0)
            return null;

        String val = value.addr();
        current = head;
        while (currPos < nodeCount && checkedPairs < filled){
            if(current.getField("filled")){
                if(current.getField("cont").equals(val))
                    return current.getField("key");
                else {
                    checkedPairs ++;
                }
            }
            currPos++;
            current = current.getField("next");
        }

        return null;
    }

    public String getValue(String key) {
        int index = hash(key) % nodeCount;

        if(filled == 0)
            return null;

        if(goTo(index)){
            int x = 1;
            int currPos = index;
            do {
                if (current.getField("filled")) {
                    if (current.getField("key").equals(key)){
                        return current.getField("cont");
                    }
                    else{
                        x++;
                        //keep searching
                        if((currPos + 1) % nodeCount < currPos){
                            currPos = (currPos + 1) % nodeCount;
                            goTo(currPos);
                        }else{
                            currPos++;
                            current = current.getField("next");
                        }
                    }
                } else return null;
            } while (currPos != index);
        }
        return null;
    }

    private void checkFilledAndCount(){
        current = head;
        int cnt = 0;
        int fill = 0;
        while(current != null){
            if(current.getField("filled"))
                fill++;
            current = current.getField("next");
            cnt++;
        }
        filled = fill;
        nodeCount = cnt;
    }

    private void checkLoad() {
        loadFactor = ((double) filled / (double) nodeCount);

        if(loadFactor > maxLoadFactor){
            //If the load factor exceeds the max load factor, remeasure filled and nodecount,
            // so that the hashmap is not iterated through on every load check
            checkFilledAndCount();
            loadFactor = ((double) filled / (double) nodeCount);
        }

        if (loadFactor > maxLoadFactor) {
            //Save the old map
            String[][] saveMap = new String[filled][2];
            current = head;
            int savedPairs = 0;
            while(savedPairs < filled && current != null){
                if(current.getField("filled")){
                    saveMap[savedPairs][0] = current.getField("key");
                    saveMap[savedPairs][1] = current.getField("cont");
                    savedPairs++;
                }
                current = current.getField("next");
            }

            current = head;
            while(current != null){
                current.setField("filled", false);
                current = current.getField("next");
            }

            //increase bucket count (i.e. add some buckets to the list)
            int newMapLen = (int) Math.round(nodeCount * resizeFactor);
            int diff = newMapLen - nodeCount;


            for(int i = 0; i < diff ;i++){
                addNode(tail);
            }


            nodeCount = countNodes();

            //Fill the expanded map
            filled = 0;
            for (String[] keyval:saveMap) {
                String key = keyval[0];
                String val = keyval[1];

                int index = hash(key) % nodeCount;

                if(goTo(index)){
                    boolean broke = false;
                    int currPos = index;
                    do {
                        if (current.getField("filled")) {
                            if (current.getField("key").equals(key)) {
                                //The key is already in the map and is simply replaced
                                current.setField("cont",val);
                                broke = true;
                            } else
                                //keep searching
                                if((currPos + 1) % nodeCount < currPos){
                                    currPos = (currPos + 1) % nodeCount;
                                    goTo(currPos);
                                }else{
                                    currPos++;
                                    current = current.getField("next");
                                }
                        } else {
                            //there is an empty slot
                            current.setField("key", key);
                            current.setField("cont", val);
                            current.setField("filled", true);
                            filled++;
                            broke = true;
                        }
                    } while (currPos != index && !broke);
                }
                System.out.print("\rReadded: " + filled + "/" + saveMap.length + "   Went to index " + index);
            }
        }
    }

    public void touchAll() throws Exception{
        //PrintWriter writer = new PrintWriter("AddressMapResults" + System.currentTimeMillis() + ".csv", "UTF-8");
        //writer.println("num, res");

        current = head;
        int x = 0;
        while(current != null){
            //long firstTime = System.nanoTime();
//            System.out.println(current.ref().filled + current.ref().key + current.ref().cont);
            current = current.ref().next;
            //long sndTime = System.nanoTime();
            //writer.println(x + "," + TimeUnit.NANOSECONDS.toMillis(sndTime - firstTime));
            x++;
        }
        //writer.close();
    }

    private int hash(String key) {
        //Taken from HashMap implementation of Java standard library
        int h;
        return Math.abs((key == null) ? 0 : (h = key.hashCode()) ^ (h >>> 16));
    }
}
