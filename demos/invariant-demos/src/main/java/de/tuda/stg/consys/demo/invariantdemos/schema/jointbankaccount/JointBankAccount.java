package de.tuda.stg.consys.demo.invariantdemos.schema.jointbankaccount;

import de.tuda.stg.consys.annotations.methods.WeakOp;
import de.tuda.stg.consys.core.legacy.CanBeMerged;

import java.io.Serializable;

public class JointBankAccount implements CanBeMerged<JointBankAccount>, Serializable {
    //@ public invariant balance >= 0;
    private int balance = 0;
    int timestamp = 0;
    private boolean requested = false;
    private boolean approved = false;


    /*@
    @ ensures balance == 0;
    @ ensures timestamp == 0;
    @ ensures requested == false;
    @ ensures approved == false;
    @*/
    public JointBankAccount() {}


    /*@
    @ requires amount >= 0;
    @ ensures balance == \old(balance) + amount;
    @ ensures timestamp == \old(timestamp) + 1;
    @ ensures requested == \old(requested);
    @ ensures approved == \old(approved);

    @*/
    @WeakOp
    public void deposit(int amount) {
        if (amount < 0) return;
        balance += amount;
        timestamp += 1;
    }

    /*@
    @ requires \old(balance) - amount >= 0;
    @ requires \old(approved) == true;
    @ ensures balance == \old(balance) - amount;
    @ ensures timestamp == \old(timestamp) + 1;
    @ ensures approved == false;
    @ ensures requested == false;
    @*/
    @WeakOp public void withdraw(int amount) {
        if (amount < 0) return;
        if (!approved) return;
        balance -= amount;
        reset();
        timestamp += 1;
    }

    /*@
    @ ensures timestamp == \old(timestamp) + 1;
    @ ensures approved == \old(approved);
    @ ensures requested == true;
    @ ensures balance == \old(balance);
    @*/
    @WeakOp public void request() {
        requested = true;
        timestamp += 1;
    }

    /*@
    @ ensures timestamp == \old(timestamp) + 1;
    @ ensures approved == \old(requested);
    @ ensures requested == \old(requested);
    @ ensures balance == \old(balance);
    @*/
    @WeakOp public void approve() {
        approved = requested;
        timestamp += 1;
    }

    /*@
    @ ensures timestamp == \old(timestamp) + 1;
    @ ensures approved == false;
    @ ensures requested == false;
    @ ensures balance == \old(balance);
    @*/
    @WeakOp public void reset() {
        requested = false;
        approved = false;
        timestamp += 1;
    }

    /*@
    @ requires \old(balance) >= 0;
    @ requires other.balance >= 0;
    @ requires \old(timestamp) == other.timestamp ==> \old(balance) == other.balance;

    @ ensures (\old(timestamp) > other.timestamp) ==> (balance == \old(balance)) && (timestamp == \old(timestamp)) && (requested == \old(requested)) && (approved == \old(approved));
    @ ensures (\old(timestamp) < other.timestamp) ==> (balance == other.balance) && (timestamp == other.timestamp) && (requested == other.requested) && (approved == other.approved);
    @ ensures (\old(timestamp) == other.timestamp) ==> (balance == \old(balance)) && (timestamp == \old(timestamp)) &&
                                                   (balance == other.balance) && (timestamp == other.timestamp) &&
                                                   (requested == \old(requested)) && (approved == \old(approved)) && (requested == other.requested) && (approved == other.approved);
    @*/
    public void merge(JointBankAccount other) {}
}
