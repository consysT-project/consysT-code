// Grow-only Counter CRDT
public class GCounterCRDT {
    public static final int numOfReplicas = 3;

    /*@
    @ public invariant getValue() >= 0;
    @ public invariant (\forall int inv1; inv1>=0 && inv1<numOfReplicas;
                          incs[inv1] >=0);
    @*/
    public int[] incs;
    public int replicaId;

    /* Constructors */
    // Constructors define the initial state of an object.
    //@ requires id >= 0 && id < numOfReplicas;
    //@ ensures (\forall int i; i >= 0 && i < numOfReplicas; incs[i] == 0);
    //@ ensures replicaId == id;
    public GCounterCRDT(int id) {
        if (!(id >= 0 && id < numOfReplicas))
            throw new IllegalArgumentException("id not in range.");
        this.incs = new int[numOfReplicas];
        this.replicaId = id;
    }


    /*@
    @ assignable \nothing;
    @ ensures \result ==
              (\sum int incInd; incInd>=0 && incInd<numOfReplicas; incs[incInd]);
    @*/
    int sumIncs() {
        int res = 0;
        for (int inc : incs) {
            res += inc;
        }
        return res;
    }

    /*@ assignable \nothing;
    @ ensures \result == (\sum int i; i >= 0 && i < numOfReplicas; incs[i]);
    @*/
    int getValue() { return sumIncs(); }



    /*@
    @ assignable incs[replicaId];
    @ ensures incs[replicaId] == \old(incs[replicaId]) + 1;
    @*/
    void inc() {
        incs[replicaId] = incs[replicaId] + 1;
    }

    /*@
    @ requires n >= 0;
    @ assignable incs[replicaId];
    @ ensures incs[replicaId] == \old(incs[replicaId]) + n;
    @*/
    void inc(int n) {
        incs[replicaId] = incs[replicaId] + n;
    }


    /*@
      @ ensures (\forall int i; i >= 0 && i < numOfReplicas;
                     (\old(incs[i]) >= other.incs[i] ? incs[i] == \old(incs[i]) : incs[i] == other.incs[i]));
      @ ensures replicaId == \old(replicaId);
    @*/
    void merge(GCounterCRDT other) {
        for (int i = 0; i < numOfReplicas; i++) {
            incs[i] = Math.max(incs[i], other.incs[i]);
        }
    }
}
