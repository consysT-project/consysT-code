package de.tuda.stg.consys.demo.invariantdemos.schema.creditaccount;

import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.core.legacy.CanBeMerged;

import java.io.Serializable;


@ReplicatedModel
public class ReplicatedCreditAccount implements Serializable, CanBeMerged<ReplicatedCreditAccount> {

    private final ReplicatedCounter credits;

    /* Invariants */
    //@ public invariant getValue() >= 0;

    //@ ensures getValue() == 0;
    //@ ensures (\forall int i; true; credits.incs[i] == 0);
    //@ ensures (\forall int i; true; credits.decs[i] == 0);
    public ReplicatedCreditAccount() {
        credits = new ReplicatedCounter();
    }

    /* Methods */
    //@ assignable \nothing;
    //@ ensures \result == \old(credits.getValue());
    @WeakOp public int getValue() {
        return credits.getValue();
    }


    //@ requires val >= 0;
    //@ assignable credits;
    //@ ensures stateful( credits.increment(val) );
    @WeakOp public void deposit(int val) {
        credits.increment(val);
    }


    //@ requires 0 <= val && val <= getValue();
    //@ assignable credits;
    //@ ensures stateful( credits.decrement(val) );
    @StrongOp public void withdraw(int val) {
        if (val > getValue()) throw new IllegalArgumentException();
        credits.decrement(val);
    }

    /* Merge method */
    //@ requires (\sum int i; i >= 0 && i < numOfReplicas(); Math.max(credits.incs[i], other.credits.incs[i])) -  (\sum int i; i >= 0 && i < numOfReplicas(); Math.max(credits.decs[i], other.credits.decs[i])) >= 0;
    //@ ensures stateful( credits.merge(other.credits) );
    public void merge(ReplicatedCreditAccount other) {
        credits.merge(other.credits);
    }
}