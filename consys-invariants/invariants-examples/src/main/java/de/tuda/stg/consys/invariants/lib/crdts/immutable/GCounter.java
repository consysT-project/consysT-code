package de.tuda.stg.consys.invariants.lib.crdts.immutable;

import de.tuda.stg.consys.Mergeable;
import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;

import static de.tuda.stg.consys.invariants.utils.InvariantUtils.numOfReplicas;
import static de.tuda.stg.consys.invariants.utils.InvariantUtils.replicaId;

import de.tuda.stg.consys.invariants.lib.Array;
import de.tuda.stg.consys.invariants.utils.InvariantUtils;


@ReplicatedModel public class GCounter implements Mergeable<GCounter> {

    public Array<Integer> increments = Array.emptyIntArray(InvariantUtils.numOfReplicas());


    /* Constructors */
    //@ ensures (\forall int i; i >= 0 && i < InvariantUtils.numOfReplicas(); increments.get(i) == 0);
    public GCounter() {

    }


    //@ assignable \nothing;
    //@ ensures \result == (\sum int i; i >= 0 && i < InvariantUtils.numOfReplicas(); (int) increments.get(i));
    public int getValue() {
        int res = 0;
        for (int inc : increments) {
            res += inc;
        }
        return res;
    }

    //@ assignable increments;
    //@ ensures increments == \old(increments.set(InvariantUtils.replicaId(), increments.get(InvariantUtils.replicaId()) + 1) );
    public Void inc() {
        inc(1);
        return null;
    }


    //@ assignable increments;
    //@ ensures increments == \old(increments.set(InvariantUtils.replicaId(), increments.get(InvariantUtils.replicaId()) + n) );
    public Void inc(int n) {
        increments = increments.set(replicaId(), increments.get(replicaId()) + n);
        return null;
    }


    //@ assignable increments;
    //@ ensures (\forall int i; i >= 0 && i < InvariantUtils.numOfReplicas(); increments == \old(increments.set(i, Math.max(increments.get(i), other.increments.get(i)))) );
    public Void merge(GCounter other) {
        for (int i = 0; i < numOfReplicas(); i++) {
            increments = increments.set(i, Math.max(increments.get(i), other.increments.get(i)));
        }

        return null;
    }
}
