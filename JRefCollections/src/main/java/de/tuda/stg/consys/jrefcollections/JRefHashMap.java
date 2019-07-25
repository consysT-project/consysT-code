package de.tuda.stg.consys.jrefcollections;

import de.tuda.stg.consys.objects.japi.JRef;

import java.io.Serializable;

public class JRefHashMap implements Serializable {

    final double maxLoadFactor = 0.75;
    final double resizeFactor = 1.4;

    private KeyJRefPair[] map = new KeyJRefPair[16];
    private double loadFactor;
    private int filled;

    class KeyJRefPair implements Serializable {
        public KeyJRefPair(String key, JRef ref) {
            this.key = key;
            this.ref = ref;
        }

        public String key;
        public JRef ref;
    }

    public int size() {
        return filled;
    }

    public JRefHashMap(int initial_size) {
        map = new KeyJRefPair[initial_size];
        filled = 0;
    }

    public JRefHashMap() {
        filled = 0;
        loadFactor = (filled / map.length);
    }

    public <T> JRef put(String key, JRef<T> value) {
        int index = hash(key) % map.length;
        int currPos = index;
        do {
            KeyJRefPair currPair = map[currPos];
            if (currPair != null) {
                if (currPair.key.equals(key)) {
                    //The key is already in the map and is simply replaced
                    map[currPos] = new KeyJRefPair(key, value);
                    return currPair.ref;
                } else
                    //keep searching
                    currPos = (currPos + 1) % map.length;
            } else {
                //there is an empty slot
                map[currPos] = new KeyJRefPair(key, value);
                filled++;
                checkLoad();
                return null;
            }
        } while (currPos != index);

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

        while (currPos < map.length && checkedPairs < filled){
            KeyJRefPair currPair = map[currPos];
            if(currPair != null){
                if(refEquals(currPair.ref, value))
                    return currPair.key;
                else {
                    checkedPairs ++;
                }
            }
            currPos++;
        }

        return null;
    }

    public <T> JRef getValue(String key) {
        int index = hash(key) % map.length;
        int currPos = index;

        if(filled == 0)
            return null;

        do {
            KeyJRefPair currPair = map[currPos];
            if (currPair != null) {
                if (currPair.key.equals(key))
                    return currPair.ref;
                else
                    currPos = (currPos + 1) % map.length;
            } else return null;
        } while (currPos != index);

        return null;
    }



    private void checkLoad() {
        loadFactor = (filled / map.length);
        if (loadFactor > maxLoadFactor) {
            //increase bucket count
            KeyJRefPair[] oldMap = map;
            map = new KeyJRefPair[(int) Math.round(oldMap.length * resizeFactor)];

            for (KeyJRefPair pair : oldMap) {
                int index = hash(pair.key) % map.length;
                int currPos = index;
                do {
                    KeyJRefPair currPair = map[currPos];
                    if (currPair != null) {
                        //keep searching
                        currPos = (currPos + 1) % map.length;
                    } else {
                        //there is an empty slot
                        map[currPos] = pair;
                        break;
                    }
                } while (currPos != index);
            }
        }
    }

    private int hash(String key) {
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
        return (ret % 2069);
    }

    /*
     * A janky method to check if two refs refer to the same item.
     */
    private boolean refEquals(JRef ref1, JRef ref2){
        return (ref1.toString().equals(ref2.toString()));
    }
}
