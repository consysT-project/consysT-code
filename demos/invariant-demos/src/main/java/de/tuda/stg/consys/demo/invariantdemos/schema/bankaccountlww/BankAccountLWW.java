package de.tuda.stg.consys.demo.invariantdemos.schema.bankaccountlww;

import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.core.legacy.CanBeMerged;

import java.io.Serializable;

public class BankAccountLWW implements CanBeMerged<BankAccountLWW>, Serializable {
    //@ public invariant balance >= 0;

    private int balance = 0;
    int timestamp = 0;

    /*@
    @ ensures balance == 0;
    @ ensures timestamp == 0;
    @*/
    public BankAccountLWW() {}

    /*@
    @ requires amount >= 0;
    @ ensures balance == \old(balance) + amount;
    @ ensures timestamp == \old(timestamp) + 1;
    @*/
    @WeakOp public void deposit(int amount) {
        if (amount < 0) throw new IllegalArgumentException("amount must be positive");
        balance += amount;
        timestamp += 1;
    }

    /*@
    @ requires \old(balance) - amount >= 0;
    @ ensures balance == \old(balance) - amount;
    @ ensures timestamp == \old(timestamp) + 1;
    @*/
    @WeakOp
    public void withdraw(int amount) {
        if (amount < 0) return;
        balance -= amount;
        timestamp += 1;
    }

    /*@
    @ requires \old(balance) >= 0;
    @ requires other.balance >= 0;
    @ requires \old(timestamp) == other.timestamp ==> \old(balance) == other.balance;

    @ ensures (\old(timestamp) > other.timestamp) ==> (balance == \old(balance)) && (timestamp == \old(timestamp));
    @ ensures (\old(timestamp) < other.timestamp) ==> (balance == other.balance) && (timestamp == other.timestamp);
    @ ensures (\old(timestamp) == other.timestamp) ==> (balance == \old(balance)) && (timestamp == \old(timestamp)) &&
                                                       (balance == other.balance) && (timestamp == other.timestamp);
    @*/
    public void merge(BankAccountLWW other) {}
}
