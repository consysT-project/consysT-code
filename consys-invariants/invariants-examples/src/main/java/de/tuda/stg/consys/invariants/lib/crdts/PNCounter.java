package de.tuda.stg.consys.invariants.lib.crdts;

// Positive Negative Counter CRDT
// TODO: we can re-implement it using GCounter and have less annotations here. Shall we consider it?

import de.tuda.stg.consys.Mergeable;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;

import static de.tuda.stg.consys.invariants.utils.InvariantUtils.numOfReplicas;
//import static de.tuda.stg.consys.invariants.utils.InvariantUtils.replicaId;


@ReplicatedModel public class PNCounter implements Mergeable<PNCounter> {


    public final int replicaId;

    public int[] incs;
    public int[] decs;

    /* Constructors */
    //@ requires replicaId == replicaId;
    //@ ensures (\forall int i; i >= 0 && i < numOfReplicas(); incs[i] == 0 && decs[i] == 0);
    public PNCounter(int replicaId) {
        this.replicaId = replicaId;
        this.incs = new int[numOfReplicas()];
        this.decs = new int[numOfReplicas()];
    }


    /*@
    @ assignable \nothing;
    @ ensures \result == (\sum int i; i >= 0 && i < numOfReplicas(); incs[i]);
    @*/
    int sumIncs() {
        int res = 0;
        for (int inc : incs) {
            res += inc;
        }
        return res;
    }

    /*@
    @ assignable \nothing;
    @ ensures \result == (\sum int i; i >= 0 && i < numOfReplicas(); decs[i]);
    @*/
    int sumDecs(){
        int result = 0;
        for (int dec : decs) {
            result += dec;
        }
        return result;
    }

    /*@
    @ assignable \nothing;
    @ ensures \result == sumIncs() - sumDecs();
    @*/
    public int getValue() { return sumIncs() - sumDecs(); }



    /*@
    @ assignable incs[replicaId];
    @ ensures incs[replicaId] == \old(incs[replicaId]) + 1;
    @*/
    public Void inc() {
        incs[replicaId] = incs[replicaId] + 1;
        return null;
    }

    /*@
    @ requires n >= 0;
    @ assignable incs[replicaId];
    @ ensures incs[replicaId] == \old(incs[replicaId]) + n;
    @*/
    public Void inc(int n) {
        incs[replicaId] = incs[replicaId] + n;
        return null;
    }

    /*@
    @ assignable decs[replicaId];
    @ ensures decs[replicaId] == \old(decs[replicaId]) + 1;
    @*/
    public Void dec() {
        if (1 > getValue())
            throw new IllegalArgumentException();
        decs[replicaId] = decs[replicaId] + 1;
        return null;
    }


    //@ requires n >= 0;
    //@ assignable decs[replicaId];
    //@ ensures decs[replicaId] == \old(decs[replicaId]) + n;
    public Void dec(int n) {
        if (n > getValue())
            throw new IllegalArgumentException();
        decs[replicaId] = decs[replicaId] + n;
        return null;
    }

    /*@ ensures (\forall int i; i >= 0 && i < numOfReplicas();
                      incs[i] == Math.max( \old(incs[i]), other.incs[i] ) && decs[i] == Math.max( \old(decs[i]), other.decs[i] )
                 );
    */
    public Void merge(PNCounter other) {
        for (int i = 0; i < numOfReplicas(); i++) {
            incs[i] = Math.max(incs[i], other.incs[i]);
            decs[i] = Math.max(decs[i], other.decs[i]);
        }
        return null;
    }
}
