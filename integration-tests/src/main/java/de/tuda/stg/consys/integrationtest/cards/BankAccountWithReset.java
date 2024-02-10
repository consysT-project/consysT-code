package de.tuda.stg.consys.integrationtest.cards;

import de.tuda.stg.consys.annotations.methods.StrongOp;
import de.tuda.stg.consys.annotations.methods.WeakOp;

public class BankAccountWithReset {
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

    /* In the CARD paper, reset is only "half-strong".
     * They can be executed with out coordination, if there is
     * no concurrent withdraws. Reset by itself does not violate
     * the invariant, hence resets only need to be executed with
     * strong consistency when there are withdraws.
     *
     * We cannot represent such effects in our system as
     * consistency is always symmetric (= withdraw and reset always have to
     * be executed strong). This is similar to Quelea or RedBlue.
     */
    @StrongOp
    public void reset() {
        balance = 0;
    }
}
