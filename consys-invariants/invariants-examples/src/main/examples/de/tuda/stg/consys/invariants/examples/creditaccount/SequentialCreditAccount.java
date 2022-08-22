package de.tuda.stg.consys.invariants.examples.creditaccount;

import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import static de.tuda.stg.consys.utils.InvariantUtils.stateful;


@ReplicatedModel
public class SequentialCreditAccount {

    private final SequentialCounter credits;

    /* Invariants */
    //@ public invariant getValue() >= 0;

    //@ ensures getValue() == 0;
    public SequentialCreditAccount() {
        credits = new SequentialCounter(0);
    }

    /* Methods */
    //@ assignable \nothing;
    //@ ensures \result == credits.getValue();
    public int getValue() {
        return credits.getValue();
    }


    //@ requires val >= 0;
    //@ assignable credits;
    //@ ensures stateful( credits.increment(val) );
    public void deposit(int val) {
        credits.increment(val);
    }


    //@ requires val >= 0;
    //@ requires val <= getValue();
    //@ assignable credits;
    //@ ensures stateful( credits.decrement(val) );
    public void withdraw(int val) {
        if (val > getValue()) throw new IllegalArgumentException();
        credits.decrement(val);
    }

    /* Merge method */
    //@ ensures stateful( credits.setValue(getValue() + other.getValue()) );
    public void merge(SequentialCreditAccount other) {
        credits.setValue(getValue() + other.getValue());
    }
}