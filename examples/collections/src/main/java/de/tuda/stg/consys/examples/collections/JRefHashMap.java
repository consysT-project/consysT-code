package de.tuda.stg.consys.examples.collections;

import de.tuda.stg.consys.core.legacy.ConsistencyLabel;
import de.tuda.stg.consys.japi.legacy.JConsistencyLevels;
import de.tuda.stg.consys.japi.legacy.JRef;
import de.tuda.stg.consys.japi.legacy.JReplicaSystem;
import de.tuda.stg.consys.japi.legacy.impl.JReplicaSystems;

import java.io.Serializable;

public class JRefHashMap implements Serializable {

    final double maxLoadFactor = 0.75;
    final double resizeFactor = 1.4;

    //private KeyJRefPair[] map = new KeyJRefPair[16];
    private JRef<JRefDistList> map;
    private double loadFactor;
    private int filled;
    private ConsistencyLabel level;


    public int size() {
        return filled;
    }

    public JRefHashMap() {
    }

    public boolean init(int initial_size, ConsistencyLabel level) {
        JReplicaSystem system = JReplicaSystems.getSystem();

        this.level = level;


        map = system.replicate(new JRefDistList(level), level);
        for(int i = 0; i < initial_size ;i++){
            JRef<KeyJRefPair> newPair = system.replicate(new KeyJRefPair("",null,false), level);
            map.invoke("append", newPair);
        }

        filled = 0;
        loadFactor = (filled / (int) map.invoke("size", true));
        return true;
    }

    public <T> JRef put(String key, JRef<T> value) {
        int mapLen = map.invoke("size", true);
        int index = hash(key, mapLen) % mapLen;
        int currPos = index;
        JRef<DistNode> currNode = map.invoke("getNodeIndex", currPos, false);
        do {
            JRef<KeyJRefPair> currPair = currNode.ref().content;
            if(level.equals(JConsistencyLevels.WEAK))
                currPair.sync();
            if (currPair.getField("valid")) {
                if (currPair.getField("key").equals(key)) {
                    //The key is already in the map and is simply replaced
                    currPair.setField("ref", value);
                    return currPair.getField("ref");
                } else
                    //keep searching
                    if((currPos + 1) % mapLen < currPos){
                        currPos = (currPos + 1) % mapLen;
                        currNode = map.invoke("getNodeIndex", currPos, false);
                    }else{
                        currPos++;
                        currNode = map.invoke("getNodeNext", currNode, 1, false);
                    }
            } else {
                //there is an empty slot
                currPair.setField("ref", value);
                currPair.setField("valid", true);
                filled++;
                checkLoad();
                return null;
            }
        } while (currPos != index);

        return null;
    }

    public boolean containsKey(String key) {
		return getValue(key) != null;
    }

    public boolean containsValue(JRef value){
		return getKey(value) != null;
    }

    public String getKey(JRef value){
        int mapLen = map.invoke("size", true);

        int currPos = 0;
        int checkedPairs = 0;

        if(filled == 0)
            return null;

        JRef<DistNode> currNode = map.invoke("getNodeIndex", currPos, false);
        while (currPos < mapLen && checkedPairs < filled){
            JRef<KeyJRefPair> currPair = currNode.getField("content");
            if(level.equals(JConsistencyLevels.WEAK))
                currPair.sync();
            if(currPair.getField("valid")){
                if(refEquals(currPair.getField("ref"), value))
                    return currPair.getField("key");
                else {
                    checkedPairs ++;
                }
            }
            currPos++;
        }

        return null;
    }

    public <T> JRef getValue(String key) {
        int mapLen = map.invoke("size", true);

        int index = hash(key, mapLen) % mapLen;
        int currPos = index;

        if(filled == 0)
            return null;

        JRef<DistNode> currNode = map.invoke("getNodeIndex", currPos, false);
        do {
            JRef<KeyJRefPair> currPair = currNode.getField("content");
            if(level.equals(JConsistencyLevels.WEAK))
                currPair.sync();
            if (currPair.getField("valid")) {
                if (currPair.getField("key").equals(key)) {
                    //The value is stored at this position
                    return currPair.getField("ref");
                } else
                    //keep searching
                    if((currPos + 1) % mapLen < currPos){
                        currPos = (currPos + 1) % mapLen;
                        currNode = map.invoke("getNodeIndex", currPos, false);
                    }else{
                        currPos++;
                        currNode = map.invoke("getNodeNext", currNode, 1, false);
                    }
            } else return null;
        } while (currPos != index);

        return null;
    }



    private void checkLoad() {
        JReplicaSystem system = JReplicaSystems.getSystem();


        int mapLen = map.invoke("size", true);

        loadFactor = (filled / mapLen);
        if (loadFactor > maxLoadFactor) {
            //increase bucket count (i.e. add some buckets to the list)
            int newMapLen = (int) Math.round(mapLen * resizeFactor);
            int diff = newMapLen - mapLen;
            for(int i = 0; i < diff ;i++){
                JRef<KeyJRefPair> newPair = system.replicate(new KeyJRefPair("",null,false), level);
                map.invoke("append", newPair);
            }
        }
    }

    private int hash(String key, int mapLen) {
        char[] chars;
        int ret = 0;

        if (key != null)
            chars = key.toCharArray();
        else {
            chars = new char[0];
            ret = 1;
        }

        for (int x = 0; x < chars.length; x++) {
            ret += (x + 1) * Character.getNumericValue(chars[x]);
        }

        //Ensure that the a useful key is returned for maps larger than 2069 (or in this case 10007
        // as the aim is maps containing 10000+ elements)
        int div = 10007;
        int mult = mapLen / div;
        if(mult<1)
            return (ret % div);
        else
            return (ret % (div * (mult + 1)));
    }

    /*
     * A janky method to check if two refs refer to the same item.
     */
    private boolean refEquals(JRef ref1, JRef ref2){
        return (ref1.toString().equals(ref2.toString()));
    }
}
