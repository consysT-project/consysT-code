import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;

// Grow-only Set CRDT
import java.util.HashSet;
import java.util.Set;

@ReplicatedModel public class GSetCRDT{
    public static final int numOfReplicas = 3;

    public Set<Integer> underlying;
    public int replicaId;

    //@ public invariant replicaId >= 0 && replicaId < numOfReplicas;

    /* Constructors */
    //@ requires id >= 0 && id < numOfReplicas;
    //@ ensures underlying.isEmpty();
    //@ ensures replicaId == id;
    public GSetCRDT(int id) {
        if (!(id >= 0 && id < numOfReplicas))
            throw new IllegalArgumentException("id not in range.");
        this.underlying = new HashSet<Integer>();
        this.replicaId = id;
    }

    /*@
    @ assignable underlying;
    @ ensures underlying.contains(val);
    @ ensures underlying.containsAll(\old(underlying));
    @*/
    void add(int val) {
        underlying.add(val);
    }

    /*@
    @ assignable \nothing;
    @ ensures \result == underlying.contains(val);
    @*/
    boolean lookup(int val){
        return underlying.contains(val);
    }

    /*@
    @ ensures (\forall int i; \old(underlying.contains(i)) || other.underlying.contains(i); underlying.contains(i));
    @ ensures (\forall int i; underlying.contains(i); \old(underlying.contains(i)) || other.underlying.contains(i));
    @ ensures replicaId == \old(replicaId);
    @*/
    void merge(GSetCRDT other) {
        underlying.addAll(other.underlying);
    }
}