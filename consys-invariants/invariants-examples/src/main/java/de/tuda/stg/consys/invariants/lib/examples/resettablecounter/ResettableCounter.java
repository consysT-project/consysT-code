package de.tuda.stg.consys.invariants.lib.examples.resettablecounter;

import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import org.checkerframework.dataflow.qual.SideEffectFree;

import static de.tuda.stg.consys.invariants.utils.InvariantUtils.numOfReplicas;
import static de.tuda.stg.consys.invariants.utils.InvariantUtils.replicaId;

@ReplicatedModel class ResettableCounter {

    //@ public invariant (\forall int inv; inv>=0 && inv<numOfReplicas(); incs[inv] >= 0);

    int[] incs;

    /*@
    @ ensures (\forall int init; init>=0 && init<numOfReplicas(); incs[init] == 0);
    @*/
    public ResettableCounter() {
        incs = new int[numOfReplicas()];
        for(int i = 0; i < numOfReplicas(); ++i)
            incs[i] = 0;
    }

    /*@
    @ assignable incs[replicaId()];
    @ ensures incs[replicaId()] == (\old(incs[replicaId()]) + 1);
    @ ensures (\forall int incInd; incInd>=0 && incInd<numOfReplicas() && incInd!=replicaId(); incs[incInd] == \old(incs[incInd]));
    @*/
    @WeakOp void inc() {incs[replicaId()] = incs[replicaId()] + 1;}

    /*@
    @ assignable incs;
    @ ensures (\forall int a; 0<=a && a<numOfReplicas(); incs[a] == 0);
    @*/
    @WeakOp void reset() {
        for(int i = 0; i < numOfReplicas(); ++i)
            incs[i] = 0;
    }


    //@ assignable \nothing;
    //@ ensures \result == (\sum int b; b>=0 && b<numOfReplicas(); incs[b]);
    @SideEffectFree @WeakOp int getValue() {
        int val = 0;
        for(int i = 0; i < numOfReplicas(); ++i)
            val += incs[i];
        return val;
    }


    /*@
    @ ensures (\forall int i; i >= 0 && i < numOfReplicas();
                   (\old(incs[i]) >= other.incs[i] ? incs[i] == \old(incs[i]) : incs[i] == other.incs[i]));
    @ ensures replicaId() == \old(replicaId());
    @*/
    void merge(ResettableCounter other) {
        for (int i = 0; i < numOfReplicas(); i++)
            incs[i] = Math.max(incs[i], other.incs[i]);
    }
}