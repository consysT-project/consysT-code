package de.tuda.stg.consys.integrationtest.cards;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;

public class JointBankAccount {
    // Invariant: balance cannot be negative
    private int balance = 0;
    private boolean requested = false;
    private boolean approved = false;

    @WeakOp
    public void deposit(int amount) {
        if (amount < 0) throw new IllegalArgumentException("amount must be positive");
        balance += amount;
    }

    @StrongOp
    public void withdraw(int amount) {
        if (amount < 0) throw new IllegalArgumentException("amount must be positive");
        if (!approved) throw new IllegalStateException("cannot withdraw from unapproved account");
        balance -= amount;
        reset();
    }

    @StrongOp
    public void request() {
        requested = true;
    }

    @StrongOp
    public void approve() {
        approved = requested;
    }

    @WeakOp
    public void reset() {
        requested = false;
        approved = false;
    }
}
