package de.tuda.stg.consys.invariants.lib.examples.bankaccountlww;

import de.tuda.stg.consys.annotations.invariants.ReplicatedModel;
import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;

import static de.tuda.stg.consys.invariants.utils.InvariantUtils.replicaId;


@ReplicatedModel public class BankAccountLWW {

    int value = 0;
    int timestamp = 0;

    //@ public invariant value >= 0;

    /*@
    @ ensures value == 0;
    @ ensures timestamp == 0;
    @*/
    public BankAccountLWW() {
    }

    /*@
    @ requires d >= 0;
    @ assignable value, timestamp;
    @ ensures value == \old(value) + d;
    @ ensures timestamp == \old(timestamp) + 1;
    @*/
    @WeakOp public void deposit(int d) {
        value = value + d;
        timestamp = timestamp + 1;
    }

    /*@
    @ requires value - w >= 0;
    @ assignable value, timestamp;
    @ ensures value == \old(value) - w;
    @ ensures timestamp == \old(timestamp) + 1;
    @*/
    @WeakOp public void withdraw(int w) {
        if (value - w < 0)
            throw new IllegalArgumentException("not enough money on account");

        value = value - w;
        timestamp = timestamp + 1;
    }

    //TODO: WHat if timestamp == other.timestamp?
    /*@
    @ ensures (\old(timestamp) >= other.timestamp) ==> (value == \old(value)) && (timestamp == \old(timestamp));
    @ ensures (\old(timestamp) < other.timestamp) ==> (value == other.value) && (timestamp == other.timestamp);
    @*/
    public void merge(BankAccountLWW other) {
        if (timestamp > other.timestamp) {
            // do not change this state
        } else {
            value = other.value;
            timestamp = other.timestamp;
        }
    }
}
