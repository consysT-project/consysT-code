package de.tuda.stg.consys.integrationtest.cards;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;

public class BankAccount {
    // Invariant: balance cannot be negative
    private int balance = 0;

    @WeakOp
    public void deposit(int amount) {
        if (amount < 0) throw new IllegalArgumentException("amount must be positive");
        balance += amount;
    }

    @StrongOp
    public void withdraw(int amount) {
        if (amount < 0) throw new IllegalArgumentException("amount must be positive");
        balance -= amount;
    }
}
