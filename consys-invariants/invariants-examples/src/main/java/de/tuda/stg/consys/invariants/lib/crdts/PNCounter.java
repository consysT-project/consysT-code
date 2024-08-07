package de.tuda.stg.consys.invariants.lib.crdts;

// Positive Negative Counter CRDT
// TODO: we can re-implement it using GCounter and have less annotations here. Shall we consider it?

import de.tuda.stg.consys.Mergeable;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import org.checkerframework.dataflow.qual.SideEffectFree;

import java.io.Serializable;

import static de.tuda.stg.consys.invariants.utils.InvariantUtils.numOfReplicas;
import static de.tuda.stg.consys.invariants.utils.InvariantUtils.replicaId;


@ReplicatedModel public class PNCounter implements Mergeable<PNCounter>, Serializable {


    public final int replicaId;

    public int[] incs;
    public int[] decs;

    /* Constructors */
    //@ ensures this.replicaId == id;
    //@ ensures (\forall int i; i >= 0 && i < numOfReplicas(); incs[i] == 0 && decs[i] == 0);
    public PNCounter(int id) {
        this.replicaId = id;
        this.incs = new int[numOfReplicas()];
        this.decs = new int[numOfReplicas()];
    }

    public PNCounter() {
        this(replicaId());
    }




    //@ assignable \nothing;
    //@ ensures \result == (\sum int i; i >= 0 && i < numOfReplicas(); incs[i]);
    @SideEffectFree
    @WeakOp int sumIncs() {
        int res = 0;
        for (int inc : incs) {
            res += inc;
        }
        return res;
    }


    //@ assignable \nothing;
    //@ ensures \result == (\sum int i; i >= 0 && i < numOfReplicas(); decs[i]);
    @SideEffectFree @WeakOp int sumDecs(){
        int result = 0;
        for (int dec : decs) {
            result += dec;
        }
        return result;
    }


    //@ assignable \nothing;
    //@ ensures \result == sumIncs() - sumDecs();
    @SideEffectFree @WeakOp public int getValue() { return sumIncs() - sumDecs(); }


    //@ assignable incs[replicaId];
    //@ ensures incs[replicaId] == \old(incs[replicaId]) + 1;
    @WeakOp public Void inc() {
        incs[replicaId] = incs[replicaId] + 1;
        return null;
    }


    //@ requires n >= 0;
    //@ assignable incs[replicaId];
    //@ ensures incs[replicaId] == \old(incs[replicaId]) + n;
    @WeakOp public Void inc(int n) {
        incs[replicaId] = incs[replicaId] + n;
        return null;
    }

    /*@
    @ assignable decs[replicaId];
    @ ensures decs[replicaId] == \old(decs[replicaId]) + 1;
    @*/
    @WeakOp public Void dec() {
        if (1 > getValue())
            throw new IllegalArgumentException();
        decs[replicaId] = decs[replicaId] + 1;
        return null;
    }


    //@ requires n >= 0;
    //@ assignable decs[replicaId];
    //@ ensures decs[replicaId] == \old(decs[replicaId]) + n;
    @WeakOp public Void dec(int n) {
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
