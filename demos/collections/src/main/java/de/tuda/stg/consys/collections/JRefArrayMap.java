package de.tuda.stg.consys.collections;

import de.tuda.stg.consys.objects.ConsistencyLevel;
import de.tuda.stg.consys.objects.actors.AkkaReplicaSystem;
import de.tuda.stg.consys.objects.japi.JConsistencyLevel;
import de.tuda.stg.consys.objects.japi.JRef;
import de.tuda.stg.consys.objects.japi.JReplicaSystem;
import de.tuda.stg.consys.objects.japi.JReplicated;

import java.io.Serializable;
import java.util.Optional;

public class JRefArrayMap implements Serializable, JReplicated {
    /*
    A JRefAddressMap, but it has arrays as nodes
     */

    /* This field is needed for JReplicated */
    public transient AkkaReplicaSystem<String> replicaSystem = null;

    final double maxLoadFactor = 0.75;
    final double resizeFactor = 1.4;

    private JRef<KeyValArrayNode> head;
    private JRef<KeyValArrayNode> tail;
    private JRef<KeyValArrayNode> current;

    ConsistencyLevel level;

    private double loadFactor;
    private int filled;
    private int nodeCount;
    private int bucketCount;
    private int arraySize;

    public int size() {
        return filled;
    }

    public JRefArrayMap() {
    }

    public boolean init(int initial_size, int arraySize, ConsistencyLevel level) throws Exception{
        Optional<JReplicaSystem> systemOptional = getSystem();
        JReplicaSystem system;
        if(systemOptional.isPresent())
            system = systemOptional.get();
        else
            return false;

        this.arraySize = arraySize;
        this.level = level;
        filled = 0;
        head = system.replicate(new KeyValArrayNode(null, null, arraySize), level);
        tail = head;
        int nodesToAdd =(int) ((double) initial_size / (double) arraySize);
        for(int i = 0;i<nodesToAdd;i++){
            addNode(tail);
        }
        nodeCount = countNodes();
        bucketCount = nodeCount*arraySize;
        loadFactor = (filled / nodeCount);
        return true;
    }

    private boolean addNode(JRef<KeyValArrayNode> previous){
        Optional<JReplicaSystem> systemOptional = getSystem();
        JReplicaSystem system;
        if(systemOptional.isPresent())
            system = systemOptional.get();
        else
            return false;

        JRef<KeyValArrayNode> newNode = system.replicate(new KeyValArrayNode(previous, previous.getField("next"), arraySize), level);
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
            goToNext();
            cnt++;
        }
        return cnt;
    }

    private boolean goToNode(int index){
        current = head;
        if(index > bucketCount - 1)
            return false;
        else{
            int curr = 0;
            while(curr < (int)((double)index/(double)arraySize)){
                goToNext();
                curr++;
            }
        }
        return true;
    }

    /*
    Takes a jref and stores its address in the hashmap
     */
    public <T> String put(String key, JRef<T> value) {
        int index = hash(key) % bucketCount;
        if(goToNode(index)){
            int currPos = index;
            String val = value.addr();
            String[][] thisNodeBuckets = current.getField("cont");
            do {
                if (thisNodeBuckets[currPos % arraySize][0] != null) {
                    if (thisNodeBuckets[currPos % arraySize][0].equals(key)) {
                        //The key is already in the map and is simply replaced
                        current.invoke("setAt", (currPos % arraySize), key, val);
                        return val;
                    } else
                        //keep searching
                        if((currPos + 1) % arraySize < (currPos % arraySize)){
                            //The next position is in the array of the next node
                            if((currPos + 1) % bucketCount < currPos){
                                //The next position is in the first node (looped around the end of the list)
                                currPos = (currPos + 1) % bucketCount;
                                goToNode(currPos);
                                thisNodeBuckets = current.getField("cont");
                            }else{
                                //The next position is in the next node
                                currPos++;
                                goToNext();
                                thisNodeBuckets = current.getField("cont");
                            }
                        }else{
                            //The next position is in the array of the current node
                            currPos++;
                        }
                } else {
                    //there is an empty slot
                    current.invoke("setAt", (currPos % arraySize), key, val);
                    filled++;
                    checkLoad();
                    return null;
                }
            } while (currPos != index);
        }
        return null;
    }

    public boolean containsKey(String key) {
        if(getValue(key) == null)
            return false;
        else
            return true;
    }

    public boolean containsValue(JRef value){
        if(getKey(value) == null)
            return false;
        else
            return true;
    }

    public String getKey(JRef value){
        int currPos = 0;
        int checkedPairs = 0;

        if(filled == 0)
            return null;

        String val = value.addr();
        current = head;
        while (currPos < bucketCount && checkedPairs < filled){
            for (String[] keyval:(String[][]) current.getField("cont")) {
                if(keyval[1].equals(val)){
                    return keyval[0];
                }else{
                    checkedPairs++;
                }
                currPos++;
            }
            goToNext();
        }

        return null;
    }

    public String getValue(String key) {
        int index = hash(key) % bucketCount;

        if(filled == 0)
            return null;

        if(goToNode(index)){
            int currPos = index;
            String[][] thisNodeBuckets = current.getField("cont");
            do {
                if (thisNodeBuckets[currPos % arraySize][0] != null) {
                    if (thisNodeBuckets[currPos % arraySize][0].equals(key)){
                        return thisNodeBuckets[currPos % arraySize][1];
                    }
                    else{
                        //keep searching
                        if((currPos + 1) % arraySize < (currPos % arraySize)){
                            //The next position is in the array of the next node
                            if((currPos + 1) % bucketCount < currPos){
                                //The next position is in the first node (looped around the end of the list)
                                currPos = (currPos + 1) % bucketCount;
                                goToNode(currPos);
                                thisNodeBuckets = current.getField("cont");
                            }else{
                                //The next position is in the next node
                                currPos++;
                                goToNext();
                                thisNodeBuckets = current.getField("cont");
                            }
                        }else{
                            //The next position is in the array of the current node
                            currPos++;
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
            String[][] thisNodeBuckets = current.getField("cont");
            for (String[] keyval:thisNodeBuckets) {
                if(keyval[0] != null)
                    fill++;
            }
            goToNext();
            cnt++;
        }
        filled = fill;
        nodeCount = cnt;
        bucketCount = nodeCount*arraySize;
    }

    private void checkLoad() {
        loadFactor = ((double) filled / (double) bucketCount);

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
                String[][] thisNodeBuckets = current.getField("cont");
                for (String[] keyval:thisNodeBuckets) {
                    if(keyval[0] != null){
                        saveMap[savedPairs] = keyval;
                        savedPairs++;
                    }

                }
                goToNext();
            }

            current = head;
            while(current != null){
                current.invoke("clear");
                goToNext();
            }

            //increase bucket count (i.e. add some buckets to the list)
            int newMapLen = (int) Math.round(nodeCount * resizeFactor);
            int diff = newMapLen - nodeCount;


            for(int i = 0; i < diff ;i++){
                addNode(tail);
            }


            nodeCount = countNodes();
            bucketCount = nodeCount * arraySize;

            //Fill the expanded map
            filled = 0;
            for (String[] keyval:saveMap) {
                String key = keyval[0];
                String val = keyval[1];

                int index = hash(key) % bucketCount;
                if(goToNode(index)){
                    boolean broke = false;
                    int currPos = index;
                    String[][] thisNodeBuckets = current.getField("cont");
                    do {
                        if (thisNodeBuckets[currPos % arraySize][0] != null) {
                            if (thisNodeBuckets[currPos % arraySize][0].equals(key)) {
                                //The key is already in the map and is simply replaced
                                current.invoke("setAt", (currPos % arraySize), key, val);
                                broke = true;
                            } else
                                //keep searching
                                if((currPos + 1) % arraySize < (currPos % arraySize)){
                                    //The next position is in the array of the next node
                                    if((currPos + 1) % bucketCount < currPos){
                                        //The next position is in the first node (looped around the end of the list)
                                        currPos = (currPos + 1) % bucketCount;
                                        goToNode(currPos);
                                        thisNodeBuckets = current.getField("cont");
                                    }else{
                                        //The next position is in the next node
                                        currPos++;
                                        goToNext();
                                        thisNodeBuckets = current.getField("cont");
                                    }
                                }else{
                                    //The next position is in the array of the current node
                                    currPos++;
                                }
                        } else {
                            //there is an empty slot
                            current.invoke("setAt", (currPos % arraySize), key, val);
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
        //PrintWriter writer = new PrintWriter("ArrayMapResults" + System.currentTimeMillis() + ".csv", "UTF-8");
        //writer.println("num, res");
        current = head;
        int x = 0;
        //long outTime = 0;
        while(current != null){
            //if(outTime == 0)
            //    outTime = System.nanoTime();

            String[][] thisNodeBuckets = current.getField("cont");
            for (String[] keyval:thisNodeBuckets) {
                //long firstTime = System.nanoTime();
                //if(outTime != 0)
                //    firstTime = outTime;

                System.out.println(keyval[0] + " - " + keyval[1]);
                //long sndTime = System.nanoTime();
                //writer.println(x + "," + TimeUnit.NANOSECONDS.toMillis(sndTime - firstTime));
                x++;
                //outTime = 0;
            }
            //outTime = System.nanoTime();
            goToNext();
        }
        //writer.close();
    }

    private int hash(String key) {
        //Taken from HashMap implementation of Java standard library
        int h;
        return Math.abs((key == null) ? 0 : (h = key.hashCode()) ^ (h >>> 16));
    }

    private boolean isLow(){
        return (JConsistencyLevel.WEAK == level);
    }

    private void goToNext(){
        if(isLow()) current.sync();
        current = current.getField("next");
    }
}

