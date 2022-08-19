package de.tuda.stg.consys.invariants.examples.creditaccount;

import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import de.tuda.stg.consys.invariants.lib.crdts.PNCounter;


@ReplicatedModel
public class ReplicatedCreditAccount {

    private final PNCounter credits;

    /* Invariants */
    //@ public invariant getValue() >= 0;

    //@ ensures getValue() == 0;
    //@ ensures (\forall int i; true; credits.incs[i] == 0);
    //@ ensures (\forall int i; true; credits.decs[i] == 0);
    public ReplicatedCreditAccount() {
        credits = new PNCounter();
    }

    /* Methods */
    //@ assignable \nothing;
    //@ ensures \result == \old(credits.getValue());
    public int getValue() {
        return credits.getValue();
    }


    //@ requires val >= 0;
    //@ assignable credits;
    //@ ensures stateful( credits.inc(val) );
    public void deposit(int val) {
        credits.inc(val);
    }


    //@ requires 0 <= val && val <= getValue();
    //@ assignable credits;
    //@ ensures stateful( credits.dec(val) );
    public void withdraw(int val) {
        if (val > getValue()) throw new IllegalArgumentException();
        credits.dec(val);
    }

    /* Merge method */
    //@ requires __merge(credits);
    //@ ensures stateful( credits.merge(other.credits) );
    public void merge(ReplicatedCreditAccount other) {
        credits.merge(other.credits);
    }
}