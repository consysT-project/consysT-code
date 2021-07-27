// Grow-only Set CRDT
import java.util.HashSet;
import java.util.Set;

public class GSetCRDT{
    public static final int numOfReplicas = 3;

    public Set<Integer> set;
    public int replicaId;


    /* Constructors */
    // Constructors define the initial state of an object.
    //@ requires id >= 0 && id < numOfReplicas;
    //@ ensures set.size() == 0;
    //@ ensures replicaId == id;
    public GSetCRDT(int id) {
        if (!(id >= 0 && id < numOfReplicas))
            throw new IllegalArgumentException("id not in range.");
        this.set = new HashSet<Integer>();
        this.replicaId = id;
    }


    /*@
    @ assignable set;
    @ ensures set.contains(val);
    @ ensures \forall Integer num; set.contains(num) && num.equals(val) == false; \old(set.contains(num));
    @*/
    void add(int val) {
        set.add(val);
    }



    /*@
    @ assignable nothing;
    @ ensures \result == set.contains(val);
    @*/
    boolean lookup(int val){
        return set.contains(val);
    }

    /*@
    @ ensures (\forall int val; \old(set.contains(val)) || other.set.contains(val); set.contains(val));
    @ ensures (\forall int val; set.contains(val); \old(set.contains(val)) || other.set.contains(val));
    @*/
    void merge(GSetCRDT other) {
        set.addAll(other.set);
    }
}