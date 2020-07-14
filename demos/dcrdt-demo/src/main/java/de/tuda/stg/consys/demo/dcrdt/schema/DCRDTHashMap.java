package de.tuda.stg.consys.demo.dcrdt.schema;

import de.tuda.stg.consys.core.akka.Delta;
import de.tuda.stg.consys.core.akka.DeltaCRDT;

import java.util.HashMap;

public class DCRDTHashMap extends DeltaCRDT{
    private HashMap<String, DeltaCRDT> internalMap = new HashMap<>();
    public Delta put(String key, DeltaCRDT object) {
        DeltaCRDT val = internalMap.get(key);
        if (val != null) {
            val.merge(object);
        } else {
            internalMap.put(key,object);
        }
        return new Delta(new Pair(key, object));
    }

    @Override
    public void merge(Object other) {
        if (other instanceof Pair) {
            Pair<String, DeltaCRDT> p = (Pair<String, DeltaCRDT>) other;
            String key = p.getKey();
            DeltaCRDT val = p.getValue();
            DeltaCRDT oldVal = internalMap.get(key);
            if (oldVal != null) {
                oldVal.merge(val);
            } else {
                internalMap.put(key,val);
            }
        }
    }

    public DeltaCRDT get(String key) {
        return internalMap.get(key);
    }
}
