package org.conloc.invariants.lib.examples.jointbankaccount;

import org.conloc.annotations.invariants.ReplicatedModel;
import org.conloc.invariants.lib.crdts.PNCounter;

import static org.conloc.invariants.utils.InvariantUtils.numOfReplicas;
import static org.conloc.invariants.utils.InvariantUtils.replicaId;
import static org.conloc.invariants.utils.InvariantUtils.stateful;

@ReplicatedModel public class JointBankAccount {
    //@ public invariant approved ? requested : true;
    private PNCounter balance;
    private boolean requested = false;
    private boolean approved = false;


    /*@
    @ ensures balance.getValue() == 0;
    @ ensures requested == false;
    @ ensures approved == false;
    @*/
    public JointBankAccount() {
        balance = new PNCounter();
    }

    /*@
    @ requires amount >= 0;
    @ assignable balance;
    @ ensures balance.getValue() == \old(balance.getValue() + amount);
    @*/
    public void deposit(int amount) {
        if (amount < 0) throw new IllegalArgumentException("amount must be positive");
        balance.inc(amount);
    }

    /*@
    @ requires amount >= 0;
    @ requires balance.getValue() - amount >= 0;
    @ requires approved == true;
    @ assignable balance, approved, requested;
    @ ensures stateful( balance.dec(amount) );
    @ ensures approved == false;
    @ ensures requested == false;
    @*/
    public void withdraw(int amount) {
        if (amount < 0) throw new IllegalArgumentException("amount must be positive");
        if (!approved) throw new IllegalStateException("cannot withdraw from unapproved account");
        balance.dec(amount);
        reset();
    }

    /*@
    @ assignable requested;
    @ ensures requested == true;
    @*/
    public void request() {
        requested = true;
    }

    /*@
    @ assignable approved;
    @ ensures approved == \old(requested);
    @*/
    public void approve() {
        approved = requested;
    }

    /*@
    @ assignable approved, requested;
    @ ensures approved == false;
    @ ensures requested == false;
    @*/
    public void reset() {
        requested = false;
        approved = false;
    }

    /*@
    @ ensures stateful( balance.merge(other.balance) );
    @ ensures requested == (\old(requested) || other.requested);
    @ ensures approved == (\old(approved) || other.approved);
    @*/
    public void merge(JointBankAccount other) {
        requested = requested || other.requested;
        approved = approved || other.approved;
        balance.merge(other.balance);
    }
}
