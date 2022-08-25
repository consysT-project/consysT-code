package de.tuda.stg.consys.demo.crdts.schema;
// Grow-only Counter CRDT

import de.tuda.stg.consys.Mergeable;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;

import java.io.Serializable;

import static de.tuda.stg.consys.invariants.utils.InvariantUtils.numOfReplicas;
import static de.tuda.stg.consys.invariants.utils.InvariantUtils.replicaId;

@SuppressWarnings("consistency")
@ReplicatedModel public class GCounter implements Mergeable<GCounter>, Serializable {

    public int[] incs;


    /* Constructors */
    //@ ensures (\forall int i; i >= 0 && i < numOfReplicas(); incs[i] == 0);
    public GCounter() {
        this.incs = new int[numOfReplicas()];
    }


    /*@
    @ assignable \nothing;
    @ ensures \result == (\sum int incInd; incInd >= 0 && incInd < numOfReplicas(); incs[incInd]);
    @*/
    public int sumIncs() {
        int res = 0;
        for (int inc : incs) {
            res += inc;
        }
        return res;
    }

    /*@
    @ assignable \nothing;
    @ ensures \result == (\sum int i; i >= 0 && i < numOfReplicas(); incs[i]);
    @*/
    public int getValue() { return sumIncs(); }

    /*@
    @ assignable incs[replicaId()];
    @ ensures incs[replicaId()] == \old(incs[replicaId()]) + 1;
    @*/
    public Void inc() {
        incs[replicaId()] = incs[replicaId()] + 1;
        return null;
    }

    /*@
    @ requires n >= 0;
    @ assignable incs[replicaId()];
    @ ensures incs[replicaId()] == \old(incs[replicaId()]) + n;
    @*/
    public Void inc(int n) {
        incs[replicaId()] = incs[replicaId()] + n;
        return null;
    }


    /*@
    @ ensures (\forall int i; i >= 0 && i < numOfReplicas(); (\old(incs[i]) >= other.incs[i] ? incs[i] == \old(incs[i]) : incs[i] == other.incs[i]) );
    @*/
    public Void merge(GCounter other) {
        for (int i = 0; i < numOfReplicas(); i++) {
            incs[i] = Math.max(incs[i], other.incs[i]);
        }
        return null;
    }
}
