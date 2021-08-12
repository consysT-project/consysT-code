import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;

import static de.tuda.stg.consys.utils.InvariantUtils.stateful;

@ReplicatedModel
public class SimpleCounter {

    public static final int numOfReplicas = 3;

    public SimpleNumber[] incs;
    public int replicaId;

    /* Constructors */
    //@ requires id >= 0 && id < numOfReplicas;
    //@ ensures (\forall int i; i >= 0 && i < numOfReplicas; incs[i].hasValue(0));
    //@ ensures replicaId == id;
    public SimpleCounter(int id) {
        if (!(id >= 0 && id < numOfReplicas))
        throw new IllegalArgumentException("id not in range.");
        this.incs = new SimpleNumber[numOfReplicas];
        for(int i = 0; i < numOfReplicas; ++i)
            incs[i].setValue(0);
    }

    /*@ assignable \nothing;
    @ ensures \result ==  (\sum int i; i >= 0 && i < numOfReplicas; incs[i].getValue());
    @*/
    int getValue() {
        int res = 0;
        for (int i = 0; i < numOfReplicas; ++i) {
            res += incs[i].getValue();
        }
        return res;
    }

    /*@ assignable incs[replicaId];
    @ ensures stateful( incs[replicaId].setValue(incs[replicaId].getValue() + 1) );
    @*/
    void inc() {
        incs[replicaId].setValue(incs[replicaId].getValue() + 1);
    }

    /*@
    @ ensures (\forall int i; i >= 0 && i < numOfReplicas;
                     \old(incs[i].getValue()) >= other.incs[i].getValue() ?
                        stateful( incs[i].setValue(incs[i].getValue()) )
                        : stateful( incs[i].setValue(other.incs[i].getValue()) ));
    @ ensures replicaId == \old(replicaId);
    @*/
    void merge(SimpleCounter other) {
        for (int i = 0; i < numOfReplicas; i++) {
            incs[i].setValue(Math.max(incs[i].getValue(), other.incs[i].getValue()));
        }
    }

}