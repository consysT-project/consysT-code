package de.tuda.stg.consys.jrefcollections;

import de.tuda.stg.consys.objects.japi.JRef;

import java.io.Serializable;

public class JRefHashMap implements Serializable {

    final double maxLoadFactor = 0.75;
    final double resizeFactor = 1.4;

    private KeyJRefPair[] map = new KeyJRefPair[16];
    private double loadFactor;
    private int filled;

    class KeyJRefPair {
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

    public <T> JRef get(String key) {
        int index = hash(key) % map.length;
        int currPos = index;
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
}
